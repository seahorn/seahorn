all: test1.c test2.c test3.c test4.c test5.c test6.c test7.c test8.c test9.c

%.c: in/%.c in/memcex.h
	$(CC) -I ../../include -E $< -o $@
