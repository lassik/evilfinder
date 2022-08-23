CFLAGS = -Wall -Wextra -pedantic -std=c99 -Og -g

all: shuffle ef

clean:
	rm -f shuffle ef core *.o core.* *~ a.out

format:
	clang-format -i *.c

.PHONY: all clean format
