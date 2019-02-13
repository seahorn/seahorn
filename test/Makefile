LIT     = $(shell which lit)
OUT_LOG = ./tests.log

test: clean
ifeq ($(LIT),)
	$(error you need to (pip) install lit)
else
	${LIT} --param=test_dir=./simple  ./simple  -v -o ${OUT_LOG}
#	${LIT} --param=test_dir=./predabs ./predabs -v -o ${OUT_LOG}
	${LIT} --param=test_dir=./solve   ./solve   -v -o ${OUT_LOG}
	${LIT} --param=test_dir=./abc     ./abc     -v -o ${OUT_LOG} 
	${LIT} --param=test_dir=./dsa     ./dsa     -v -o ${OUT_LOG}
	${LIT} --param=test_dir=./inc     ./inc     -v -o ${OUT_LOG}
	${LIT} --param=test_dir=./formats ./formats -v 
endif

clean:
	rm -f ${OUT_LOG}
