/* 
   This code randomizes the order of lines in a file. Based on a tool
   'randomize' by Jef Poskanzer <jef@acme.com>.

   I tweaked it a bit to work better with evilfinder. All lines that
   do not start with digit or * and digit are ignored, short lines are
   ignored, max line length is 1024, randomness is taken from /dev/urandom.

 */

#include <stdio.h>
#include <string.h>
#include <stdlib.h>
#include <unistd.h>
#include <fcntl.h>
#include <ctype.h>

#define MAXLINE 1024


int rf=-1;

unsigned int get_random(void) {
  int val;
  if (rf<0) {
    rf=open("/dev/urandom",O_RDONLY);
    if (rf<0) { perror("/dev/urandom"); exit(1); }
  }
  read(rf,&val,4);
  return val;
}


int main(void) {
  int    i, j, maxlines, nlines;
  char   line[MAXLINE];
  char** lines;
  char*  t;

  maxlines = 500;
  lines = (char**) malloc( maxlines * sizeof(char*) );
  nlines = 0;

  while (fgets(line,MAXLINE,stdin)) {

    if (strlen(line)<5) continue;
    if (!(isdigit(line[0]) || (line[0]=='*' && isdigit(line[1])))) continue;

    if (nlines>=maxlines) {
      maxlines += 10000;
      lines = (char**)realloc((char*)lines,maxlines*sizeof(char*));
    }

    lines[nlines] = (char*)malloc(strlen(line)+1);
    strcpy(lines[nlines],line);
    nlines++;

  }

  for (i=0;i<nlines;++i) {
    j=get_random() % nlines;
    t=lines[j];
    lines[j]=lines[i];
    lines[i]=t;
  }

  for (i=0;i<nlines;++i) fputs(lines[i],stdout);

  exit(0);

}
