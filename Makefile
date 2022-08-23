
CFLAGS = -ggdb -Wall -O9 -fomit-frame-pointer -funroll-loops -fexpensive-optimizations -ffast-math

all: shuffle ef

clean:
	rm -f shuffle ef core *.o core.* *~ a.out

publish: clean
	cd /; \
	tar cfvz ef.tgz /evilfinder; \
	scp ef.tgz lcamtuf@coredump.cx:/export/www/lcamtuf/ -p; \
	rm -f ef.tgz
