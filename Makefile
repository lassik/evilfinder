CFLAGS = -Wall -Wextra -pedantic -std=c99 -Og -g

all: shuffle ef

clean:
	rm -f shuffle ef core *.o core.* *~ a.out
