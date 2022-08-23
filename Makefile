CFLAGS = -Wall -Wextra -pedantic -std=c99 -Og -g

all: ef

clean:
	rm -f ef core *.o core.* *~ a.out

format:
	clang-format -i *.c

.PHONY: all clean format
