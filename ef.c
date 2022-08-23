/*
   The Evil Finder
   Copyright (C) 2002 by Michal Zalewski <lcamtuf@coredump.cx>
*/

#include <stdio.h>
#include <unistd.h>
#include <stdlib.h>
#include <string.h>
#include <fcntl.h>
#include <ctype.h>
#include <sys/time.h>
#include <signal.h>

#define MIN_INPUT_LEN 4
#define MAX_INPUT_LEN 100

#define MAXOPT 1024
#define MAXBUF 1024
#define MINNEST 3
#define MAXNEST 5

#define MAXRES 1

struct Trec {
  int num;
  char* desc;
};


struct proof {
  int nest;
  char* prolog;
  int usednum[MAXNEST + 2];
  int utop;
  char how[MAXBUF];
  int val;
};


struct Trec options[MAXOPT];
struct Trec final[MAXOPT];

char* rprolog[MAXRES];
char* results[MAXRES];
int restop;


int opttop, fintop;

#define fatal(x) exit(printf("<p><font color=red><b>FATAL: <i>%s</i></b></font>", x) ? 1 : 1)


static int backwardize(int z) {
  // Laaame.
  char buf[128], b2[128];
  int i, q;
  if (z < 0) return -31337000;
  sprintf(buf, "%d", z);
  q = strlen(buf);
  for (i = 0; i < q; i++) b2[q - i - 1] = buf[i];
  b2[q] = 0;
  if (!strcmp(b2, buf)) return -31337000;
  return atoi(b2);
}

static char* backstring(int z) {
  // Laaame.
  char buf[128];
  static char b2[128];
  int i, q;
  if (z < 0) return "<error>";
  sprintf(buf, "%d", z);
  q = strlen(buf);
  for (i = 0; i < q; i++) b2[q - i - 1] = buf[i];
  b2[q] = 0;
  if (!strcmp(b2, buf)) return "<error>";
  return b2;
}


static int tooctal(int z) {
  // Laaame.
  char buf[128];
  if (z < 0) return -31337000;
  sprintf(buf, "%o", z);
  if (atoi(buf) == z) return -31337000;
  return atoi(buf);
}


int rf = -1;

static unsigned int get_random(void) {
  int val;
  if (rf < 0) {
    rf = open("/dev/urandom", O_RDONLY);
    if (rf < 0) {
      perror("/dev/urandom");
      exit(1);
    }
  }
  read(rf, &val, 4);
  return val;
}


static void trace_proof(struct proof* p) {
  int i, a;
  char order[12] = {0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11};


  // Whoops. Bail out.
  if (restop >= MAXRES) return;

  // Check for "proven' conditions.
  if (p->nest >= MINNEST && p->val > 0)

    for (i = 0; i < fintop; i++) {
      // Straight
      if (p->val == final[i].num) {
        char buf[MAXBUF * 2];
        strcpy(buf, p->how);
        sprintf(&buf[strlen(buf)], "The number %d is %s.\n<p>\n<b>This clearly proves how evil the subject is. QED.\n", final[i].num, final[i].desc);
        rprolog[restop] = p->prolog;
        results[restop++] = strdup(buf);
        //      printf("PROOF %d: %s\n",restop,buf);
        return;
      }

      // In reverse
      if (p->val == backwardize(final[i].num)) {
        char buf[MAXBUF * 2];
        strcpy(buf, p->how);
        sprintf(&buf[strlen(buf)], "This number, read from right to left, is %d, or %s.\n<p>\n<b>No further questions. QED.\n", final[i].num, final[i].desc);
        rprolog[restop] = p->prolog;
        results[restop++] = strdup(buf);
        //      printf("PROOF %d: %s\n",restop,buf);
        return;
      }

      // The result in octal is...
      if (tooctal(p->val) == final[i].num) {
        char buf[MAXBUF * 2];
        strcpy(buf, p->how);
        sprintf(&buf[strlen(buf)], "This, written in octal, is %d, %s.\n<p>\n<b>It speaks for itself. QED.\n", final[i].num, final[i].desc);
        rprolog[restop] = p->prolog;
        results[restop++] = strdup(buf);
        //      printf("PROOF %d: %s\n",restop,buf);
        return;
      }

      // The result is ..., which in octal...
      if (p->val == tooctal(final[i].num)) {
        char buf[MAXBUF * 2];
        strcpy(buf, p->how);
        sprintf(&buf[strlen(buf)], "This number, read as octal, gives %d - %s.\n<p>\n<b>This is truly evil. QED.\n", final[i].num, final[i].desc);
        rprolog[restop] = p->prolog;
        results[restop++] = strdup(buf);
        //      printf("PROOF %d: %s\n",restop,buf);
        return;
      }

      // The result in octal is ... backwards
      if (tooctal(p->val) == backwardize(final[i].num) && tooctal(p->val) > 0) {
        char buf[MAXBUF * 2];
        strcpy(buf, p->how);
        sprintf(&buf[strlen(buf)], "This, written in octal, is %d. This, read backwards, gives %d, %s.\n<p>\n<b>No doubt about its evilness. QED.\n", tooctal(p->val), final[i].num, final[i].desc);
        rprolog[restop] = p->prolog;
        results[restop++] = strdup(buf);
        //      printf("PROOF %d: %s\n",restop,buf);
        return;
      }

      // The result is ..., which in octal is ... backwards
      if (backwardize(p->val) == tooctal(final[i].num) && backwardize(p->val) > 0) {
        char buf[MAXBUF * 2];
        strcpy(buf, p->how);
        sprintf(&buf[strlen(buf)], "This, when read backwards, gives %s. This is %d in octal, %s...\n<p>\n<b>Evil, QED.\n", backstring(p->val), final[i].num, final[i].desc);
        rprolog[restop] = p->prolog;
        results[restop++] = strdup(buf);
        //      printf("PROOF %d: %s\n",restop,buf);
        return;
      }

      // The result backwards in octal is ...
      if (tooctal(backwardize(p->val)) == final[i].num) {
        char buf[MAXBUF * 2];
        strcpy(buf, p->how);
        sprintf(&buf[strlen(buf)], "This number, when read backwards, gives %s. This, written in octal, gives %d - %s.\n<p>\n<b>Enough said - QED.\n", backstring(p->val), final[i].num, final[i].desc);
        rprolog[restop] = p->prolog;
        results[restop++] = strdup(buf);
        //      printf("PROOF %d: %s\n",restop,buf);
        return;
      }

      // The result in octal is ... backwards
      if (p->val == tooctal(backwardize(final[i].num))) {
        char buf[MAXBUF * 2];
        strcpy(buf, p->how);
        sprintf(&buf[strlen(buf)], "Write %d backwards. Translate it to octal - this will give you %d. Thus, %d stands for %d, %s.\n<p>\n<b>You get the picture. QED.\n", final[i].num, p->val, p->val, final[i].num, final[i].desc);
        rprolog[restop] = p->prolog;
        results[restop++] = strdup(buf);
        //      printf("PROOF %d: %s\n",restop,buf);
        return;
      }
    }

  // Nest level exceeded. Abandon this branch.
  if (p->nest >= MAXNEST) return;

  // Now, let's try all possibilities:

  // Shuffle check order
  for (i = 0; i < 12; i++) {
    char tmp;
    int z = get_random() % 12;
    tmp = order[i];
    order[i] = order[z];
    order[z] = tmp;
  }

  for (a = 0; a < 12; a++)
    switch (order[a]) {
    case 0:
      // Straight addition
      for (i = 0; i < opttop; i++) {
        struct proof* n;
        int t;
        for (t = 0; t < p->utop; t++)
          if (options[i].num == p->usednum[t]) goto skip1;
        n = malloc(sizeof(struct proof));
        memcpy(n, p, sizeof(struct proof));
        n->val = p->val + options[i].num;
        n->usednum[n->utop++] = options[i].num;
        n->nest++;
        sprintf(&n->how[strlen(n->how)], "Add %d, %s - the result is %d.\n<p>\n", options[i].num, options[i].desc, n->val);
        trace_proof(n);
        free(n);
skip1:
        break;
      }
      break;


    case 1:
      // Right reverse addition
      for (i = 0; i < opttop; i++) {
        struct proof* n;
        int t;
        if (backwardize(options[i].num) < 0) continue;
        for (t = 0; t < p->utop; t++)
          if (options[i].num == p->usednum[t]) goto skip2;
        n = malloc(sizeof(struct proof));
        memcpy(n, p, sizeof(struct proof));
        n->val = p->val + backwardize(options[i].num);
        n->usednum[n->utop++] = options[i].num;
        n->nest++;
        sprintf(&n->how[strlen(n->how)], "Add %s to it - this is %s, written backwards - you will get %d.\n<p>\n", backstring(options[i].num), options[i].desc, n->val);
        trace_proof(n);
        free(n);
skip2:
        break;
      }
      break;


    case 2:
      // Left reverse addition
      for (i = 0; i < opttop; i++) {
        struct proof* n;
        int t;
        if (backwardize(p->val) < 0) continue;
        for (t = 0; t < p->utop; t++)
          if (options[i].num == p->usednum[t]) goto skip3;
        n = malloc(sizeof(struct proof));
        memcpy(n, p, sizeof(struct proof));
        n->usednum[n->utop++] = options[i].num;
        n->val = backwardize(p->val) + options[i].num;
        n->nest++;
        sprintf(&n->how[strlen(n->how)], "Turn the number backwards, and add %d - %s. The number is now %d.\n<p>\n", options[i].num, options[i].desc, n->val);
        trace_proof(n);
        free(n);
skip3:
        break;
      }
      break;

    case 3:
      // Straight subtraction
      for (i = 0; i < opttop; i++) {
        struct proof* n;
        int t;
        if (p->val - options[i].num < 100) continue;
        for (t = 0; t < p->utop; t++)
          if (options[i].num == p->usednum[t]) goto skip4;
        n = malloc(sizeof(struct proof));
        memcpy(n, p, sizeof(struct proof));
        n->val = p->val - options[i].num;
        n->usednum[n->utop++] = options[i].num;
        n->nest++;
        sprintf(&n->how[strlen(n->how)], "Subtract %d, %s. The result will be %d.\n<p>\n", options[i].num, options[i].desc, n->val);
        trace_proof(n);
        free(n);
skip4:
        break;
      }
      break;

    case 4:
      // Right reverse subtraction
      for (i = 0; i < opttop; i++) {
        struct proof* n;
        int t;
        if (p->val - backwardize(options[i].num) < 100) continue;
        for (t = 0; t < p->utop; t++)
          if (options[i].num == p->usednum[t]) goto skip5;
        n = malloc(sizeof(struct proof));
        memcpy(n, p, sizeof(struct proof));
        n->val = p->val - backwardize(options[i].num);
        n->usednum[n->utop++] = options[i].num;
        n->nest++;
        sprintf(&n->how[strlen(n->how)], "Subtract %s from the number - this is %s, written backwards. It gives %d.\n<p>\n", backstring(options[i].num), options[i].desc, n->val);
        trace_proof(n);
        free(n);
skip5:
        break;
      }
      break;

    case 5:
      // Left reverse subtraction
      for (i = 0; i < opttop; i++) {
        struct proof* n;
        int t;
        if (backwardize(p->val) - options[i].num < 100) continue;
        for (t = 0; t < p->utop; t++)
          if (options[i].num == p->usednum[t]) goto skip6;
        n = malloc(sizeof(struct proof));
        memcpy(n, p, sizeof(struct proof));
        n->val = backwardize(p->val) - options[i].num;
        n->usednum[n->utop++] = options[i].num;
        n->nest++;
        sprintf(&n->how[strlen(n->how)], "Turn the number backwards, subtract %d - %s. The number is now %d.\n<p>\n", options[i].num, options[i].desc, n->val);
        trace_proof(n);
        free(n);
skip6:
        break;
      }
      break;

    case 6:
      // Straight multiplication
      for (i = 0; i < opttop; i++) {
        struct proof* n;
        int t;
        if (p->val * options[i].num > 30000) continue;
        for (t = 0; t < p->utop; t++)
          if (options[i].num == p->usednum[t]) goto skip7;
        if (options[i].num == 1) continue;
        n = malloc(sizeof(struct proof));
        memcpy(n, p, sizeof(struct proof));
        n->val = p->val * options[i].num;
        n->usednum[n->utop++] = options[i].num;
        n->nest++;
        sprintf(&n->how[strlen(n->how)], "Multiply it by %d, %s - the number is now %d.\n<p>\n", options[i].num, options[i].desc, n->val);
        trace_proof(n);
        free(n);
skip7:
        break;
      }
      break;

    case 7:
      // Right reverse multiplication
      for (i = 0; i < opttop; i++) {
        struct proof* n;
        int t;
        if (backwardize(options[i].num) < 0) continue;
        if (p->val * backwardize(options[i].num) > 30000) continue;
        if (options[i].num == 1) continue;
        for (t = 0; t < p->utop; t++)
          if (options[i].num == p->usednum[t]) goto skip8;
        n = malloc(sizeof(struct proof));
        memcpy(n, p, sizeof(struct proof));
        n->val = p->val * backwardize(options[i].num);
        n->usednum[n->utop++] = options[i].num;
        n->nest++;
        sprintf(&n->how[strlen(n->how)], "Multiply the number by %s - this is %s, from right to left. It gives %d.\n<p>\n", backstring(options[i].num), options[i].desc, n->val);
        trace_proof(n);
        free(n);
skip8:
        break;
      }
      break;

    case 8:
      // Left reverse multiplication
      for (i = 0; i < opttop; i++) {
        struct proof* n;
        int t;
        if (backwardize(p->val) < 0) continue;
        if (backwardize(p->val) * options[i].num > 30000) continue;
        if (options[i].num == 1) continue;
        for (t = 0; t < p->utop; t++)
          if (options[i].num == p->usednum[t]) goto skip9;
        n = malloc(sizeof(struct proof));
        memcpy(n, p, sizeof(struct proof));
        n->val = backwardize(p->val) * options[i].num;
        n->usednum[n->utop++] = options[i].num;
        n->nest++;
        sprintf(&n->how[strlen(n->how)], "Turn the number backwards, multiply by %d - %s. The number is now %d.\n<p>\n", options[i].num, options[i].desc, n->val);
        trace_proof(n);
        free(n);
skip9:
        break;
      }
      break;

    case 9:
      // Straight division
      for (i = 0; i < opttop; i++) {
        struct proof* n;
        int t;
        if (p->val % options[i].num) continue;
        if (p->val / options[i].num < 100) continue;
        if (options[i].num == 1) continue;
        for (t = 0; t < p->utop; t++)
          if (options[i].num == p->usednum[t]) goto skip10;
        n = malloc(sizeof(struct proof));
        memcpy(n, p, sizeof(struct proof));
        n->val = p->val / options[i].num;
        n->usednum[n->utop++] = options[i].num;
        n->nest++;
        sprintf(&n->how[strlen(n->how)], "Divide by %d, %s - the result is %d.\n<p>\n", options[i].num, options[i].desc, n->val);
        trace_proof(n);
        free(n);
skip10:
        break;
      }
      break;

    case 10:
      // Right reverse division
      for (i = 0; i < opttop; i++) {
        struct proof* n;
        int t;
        if (p->val % backwardize(options[i].num)) continue;
        if (p->val / backwardize(options[i].num) < 100) continue;
        if (options[i].num == 1) continue;
        for (t = 0; t < p->utop; t++)
          if (options[i].num == p->usednum[t]) goto skip11;
        n = malloc(sizeof(struct proof));
        memcpy(n, p, sizeof(struct proof));
        n->val = p->val / backwardize(options[i].num);
        n->usednum[n->utop++] = options[i].num;
        n->nest++;
        sprintf(&n->how[strlen(n->how)], "Divide the number by %s - this is %s, backwards. It gives %d.\n<p>\n", backstring(options[i].num), options[i].desc, n->val);
        trace_proof(n);
        free(n);
skip11:
        break;
      }
      break;

    case 11:
      // Left reverse division
      for (i = 0; i < opttop; i++) {
        struct proof* n;
        int t;
        if (backwardize(p->val) % options[i].num) continue;
        if (backwardize(p->val) / options[i].num < 100) continue;
        if (options[i].num == 1) continue;
        for (t = 0; t < p->utop; t++)
          if (options[i].num == p->usednum[t]) goto skip12;
        n = malloc(sizeof(struct proof));
        memcpy(n, p, sizeof(struct proof));
        n->val = backwardize(p->val) / options[i].num;
        n->usednum[n->utop++] = options[i].num;
        n->nest++;
        sprintf(&n->how[strlen(n->how)], "Turn the number backwards, divide by %d - %s. The number is now %d.\n<p>\n", options[i].num, options[i].desc, n->val);
        trace_proof(n);
        free(n);
skip12:
        break;
      }
      break;

    default: fatal("Whoops.\n");
    }

  // Ok. All set.
}


int mypow(int what, int cnt) {
  int i, res = 1;
  for (i = 0; i < cnt; i++) res *= what;
  return res;
}


int simplify(int what) {
  while (what > 9) what = (what / 10) + (what % 10);
  return what;
}


int stopped;
int retrynum;

void interrupter(int x) {
  (void)x;
  restop = MAXRES + 1;
  // printf("...restart.\n");
  stopped = 1;
  retrynum++;
}


int asum[10], nsum[10];

int main(void) {
  int z, i, ch = 0;
  FILE* f;
  char ibuf[1024], tmp[256];


  // We assume we're not in /tmp... how convinient!
  sprintf(tmp, ".tmp-%d-%u", getpid(), (int)time(0));
  sprintf(ibuf, "./shuffle <evilnumbers.dat >%s", tmp);
  system(ibuf);

  f = fopen(tmp, "r");
  if (!f) fatal("cannot open tmp file\n");
  unlink(tmp);

  while (fgets(ibuf, sizeof(ibuf), f)) {
    int num;
    char* d;
    if (ibuf[0] == '*')
      num = atoi(&ibuf[1]);
    else
      num = atoi(ibuf);
    d = ibuf;
    while (*d && *d != ' ' && *d != '\t') d++;
    if (!*d) fatal("malformed config file\n");
    while (*d == ' ' || *d == '\t') d++;
    if (!strlen(d)) fatal("empty description in config file?\n");
    if (strchr(d, '\n')) *strchr(d, '\n') = 0;
    if (ibuf[0] == '*') {
      final[fintop].num = num;
      final[fintop].desc = strdup(d);
      fintop++;
    } else {
      options[opttop].num = num;
      options[opttop].desc = strdup(d);
      opttop++;
    }
  }

  if (!opttop) fatal("no entries in the config file.\n");
  if (!fintop) fatal("no exit conditions in the config file.\n");

  fclose(f);

  // printf("Loaded %d config entries, %d of which are exit conditions.\n",opttop,fintop);

  {
    char* x;
    x = getenv("QUERY_STRING_UNESCAPED");
    if (!x) fatal("no input provided.\n");
    if (strlen(x) > MAX_INPUT_LEN)
      fatal("suspiciously long input.\n");
    if (!strchr(x, '=')) fatal("malformed query string.\n");
    x = strchr(x, '=') + 1;
    strcpy(ibuf, x);
  }

  if (strlen(ibuf) < MIN_INPUT_LEN)
    fatal("input too short.\n");
  for (i = 0; i < (int)(strlen(ibuf)); i++)
    if (isalpha(ibuf[i])) ch++;
  if (ch < 4) fatal("not enough characters (letters).\n");
  if (strlen(ibuf) > 40) fatal("too many characters.\n");
  if (strchr(ibuf, '<')) fatal("go cross-script yourself.\n");

  z = 0;

  for (i = 0; i < ch; i++) {
    int cur = i / (ch / 4);
    while (!isalpha(ibuf[z])) z++;
    if (cur > 4) cur = 4;
    asum[cur] += simplify(toupper(ibuf[z]));
    nsum[cur] += simplify(toupper(ibuf[z]) - 'A' + 1);
    z++;
  }

  for (i = 0; i < 10; i++) {
    asum[i] = simplify(asum[i]);
    nsum[i] = simplify(nsum[i]);
  }

  // printf("asum = %d%d%d%d%d nsum = %d%d%d%d%d (chars = %d)\n",
  //      asum[0],asum[1],asum[2],asum[3],asum[4],
  //      nsum[0],nsum[1],nsum[2],nsum[3],nsum[4],ch);

retry:

  stopped = 0;
  restop = 0;
  signal(SIGALRM, interrupter);
  alarm(5 + retrynum);

  if (get_random() % 2)

  {
    struct proof p;
    int pcur = -1;
    char t[10000];
    bzero(t, sizeof(t));
    bzero(&p, sizeof(p));
    z = 0;
    for (i = 0; i < ch; i++) {
      while (!isalpha(ibuf[z])) z++;
      t[strlen(t)] = ' ';
      t[strlen(t)] = ' ';
      t[strlen(t)] = ' ';
      t[strlen(t)] = toupper(ibuf[z]);
      z++;
    }
    strcat(t, "\n");
    z = 0;
    for (i = 0; i < ch; i++) {
      while (!isalpha(ibuf[z])) z++;
      sprintf(&t[strlen(t)], "  %2d", toupper(ibuf[z]) - 'A' + 1);
      z++;
    }
    strcat(t, "     - as numbers\n");

    z = 0;
    for (i = 0; i < ch; i++) {
      while (!isalpha(ibuf[z])) z++;
      sprintf(&t[strlen(t)], "   %d", simplify(toupper(ibuf[z]) - 'A' + 1));
      z++;
    }
    strcat(t, "     - digits added\n ");

    for (i = 0; i < ch; i++) {
      int cur = i / (ch / 4);
      if (cur > 4) cur = 4;
      if (pcur != cur) {
        if (pcur != -1) strcat(t, "/");
        strcat(t, " \\_");
      } else
        strcat(t, "____");
      pcur = cur;
    }

    strcat(t, "/\n");

    for (i = 0; i < ch; i++) {
      int cur = i / (ch / 4);
      if (cur > 4) cur = 4;
      if (pcur != cur)
        sprintf(&t[strlen(t)], "   %d", nsum[cur]);
      else
        strcat(t, "    ");
      pcur = cur;
    }

    strcat(t, "     - digits added\n\n");

    if (!nsum[4])
      p.val = nsum[0] * 1000 + nsum[1] * 100 + nsum[2] * 10 + nsum[3];
    else
      p.val = nsum[0] * 10000 + nsum[1] * 1000 + nsum[2] * 100 + nsum[3] * 10 + nsum[4];

    sprintf(&t[strlen(t)], "Thus, \"%s\" is %d.\n\n", ibuf, p.val);

    p.prolog = strdup(t);
    p.usednum[0] = p.val;
    p.utop = 1;

    trace_proof(&p);

  }

  else

  {
    struct proof p;
    int pcur = -1;
    char t[10000];
    bzero(&p, sizeof(p));
    bzero(t, sizeof(t));
    z = 0;
    for (i = 0; i < ch; i++) {
      while (!isalpha(ibuf[z])) z++;
      t[strlen(t)] = ' ';
      t[strlen(t)] = ' ';
      t[strlen(t)] = ' ';
      t[strlen(t)] = toupper(ibuf[z]);
      z++;
    }
    strcat(t, "\n");
    z = 0;
    for (i = 0; i < ch; i++) {
      while (!isalpha(ibuf[z])) z++;
      sprintf(&t[strlen(t)], "  %2d", toupper(ibuf[z]));
      z++;
    }
    strcat(t, "     - as ASCII values\n");

    z = 0;
    for (i = 0; i < ch; i++) {
      while (!isalpha(ibuf[z])) z++;
      sprintf(&t[strlen(t)], "   %d", simplify(toupper(ibuf[z])));
      z++;
    }
    strcat(t, "     - digits added\n ");

    for (i = 0; i < ch; i++) {
      int cur = i / (ch / 4);
      if (cur > 4) cur = 4;
      if (pcur != cur) {
        if (pcur != -1) strcat(t, "/");
        strcat(t, " \\_");
      } else
        strcat(t, "____");
      pcur = cur;
    }

    strcat(t, "/\n");

    for (i = 0; i < ch; i++) {
      int cur = i / (ch / 4);
      if (cur > 4) cur = 4;
      if (pcur != cur)
        sprintf(&t[strlen(t)], "   %d", asum[cur]);
      else
        strcat(t, "    ");
      pcur = cur;
    }

    strcat(t, "     - digits added\n\n");

    if (!asum[4])
      p.val = asum[0] * 1000 + asum[1] * 100 + asum[2] * 10 + asum[3];
    else
      p.val = asum[0] * 10000 + asum[1] * 1000 + asum[2] * 100 + asum[3] * 10 + asum[4];

    sprintf(&t[strlen(t)], "Thus, \"%s\" is %d.\n\n", ibuf, p.val);

    p.prolog = strdup(t);
    p.usednum[0] = p.val;
    p.utop = 1;

    trace_proof(&p);
  }

  alarm(0);

  if (stopped) {
    if (retrynum < 5) goto retry;
    fatal("System timeout.\n");
  }


  if (!restop) fatal("There is no way to prove the evilness of this!\n");

  // Get random result

  z = get_random() % restop;
  printf("<b>**** THE PROOF THAT <i>%s</i> IS EVIL ****</b>\n<p>\n<pre>%s</pre>\n\n<p>%s\n", ibuf, rprolog[z], results[z]);

  return 0;
}
