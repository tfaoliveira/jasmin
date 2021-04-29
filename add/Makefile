default: add4.s addN.s addNv2.s addNv3.s addN_s.ec addN_ct.ec addNv3_ct.ec
	@true

%.s: %.jazz
	jasminc -o $@ $<

# compile implementation of add function from addN.jazz into EasyCrypt
%_s.ec: %.jazz
	jasminc -oec $@ -ec add $<

# extract EasyCrypt code for constant-time proof
%_ct.ec: %.jazz
	jasminc -CT -oec $@ -ec add $<

