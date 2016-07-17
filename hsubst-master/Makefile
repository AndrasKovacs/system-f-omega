AGDA=agda
# Specify flags on command line, e.g.
#
#   F="-i ~/local/opt/agda-std-lib/src/ -i ." make
FLAGS:=$(F)

SRC=hsubst.agda lemmas1.agda lemmas2.agda lemmas3.agda lemmas4.agda proofs.agda
OBJ=$(SRC:.agda=.agdai)


all: proofs.agdai


%.agdai: %.agda
	$(AGDA) $(FLAGS) $^


clean:
	rm -f $(OBJ) *~
