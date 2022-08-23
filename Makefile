CFLAGS = -Wall -Wextra -pedantic -std=c99 -Og -g

all: evilfinder

evilfinder: evilfinder.c
	$(CC) $(CFLAGS) -o $@ $<

clean:
	rm -f evilfinder core core.* *~

format:
	clang-format -i evilfinder.c

.PHONY: all clean format
