CFLAGS = -ggdb -Wall -O9 -fomit-frame-pointer -funroll-loops -fexpensive-optimizations -ffast-math

all: shuffle ef

clean:
	rm -f shuffle ef core *.o core.* *~ a.out
