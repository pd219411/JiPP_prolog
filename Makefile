SICSTUSHOME=/opt/sicstus4.2.1
SICSTUSBIN= $(SICSTUSHOME)/bin
PL = $(SICSTUSBIN)/sicstus
SPLD = spld
SPLDFLAGS = --static --exechome=$(SICSTUSBIN)

ALL = drzewa

all: $(ALL)

%: %.sav
	$(SPLD) $(SPLDFLAGS) $< -o $@ 

%.sav: %.pro
	echo "compile('$<'). save_program('$@')." | $(PL)

clean:
	rm -f $(ALL) *.sav
