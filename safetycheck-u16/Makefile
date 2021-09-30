%.s: %.jazz
	jasminc -o $@ $<

%.cs: %.jazz
	(jasminc -checksafety $< || touch $@.FIXME) >$@ 2>&1

SRC:= $(sort $(wildcard *.jazz))
ASM:= $(patsubst %.jazz,%.s,$(SRC))
CHECKSAFETY:= $(patsubst %.jazz,%.cs,$(SRC))
TST:= $(patsubst %.jazz,main%,$(SRC))

stuff: $(ASM) $(CHECKSAFETY)
	$(CC) -DFUNCTION=e1_while_scale -o main1 main1.c 1.s
	$(CC) -DFUNCTION=e2_while_no_scale -o main2 main1.c 2.s
	$(CC) -DFUNCTION=e3_while_scale -o main3 main3.c 3.s
	$(CC) -DFUNCTION=e4_while_scale -o main4 main3.c 4.s
	$(CC) -DFUNCTION=e5_while_scale -o main5 main3.c 5.s
	$(CC) -DFUNCTION=e6_while_scale -o main6 main3.c 6.s
	$(CC) -DFUNCTION=e7_while_no_scale -o main7 main3.c 7.s

run: stuff
	for n in 1 2 3 4 5 6 7 ; do \
		./main$$n ; \
	done
  
clean:
	rm -f $(ASM) $(CHECKSAFETY) $(TST) *.FIXME
