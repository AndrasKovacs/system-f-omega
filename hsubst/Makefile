AGDA=agda
FLAGS=

SRC=hsubst.agda lemmas1.agda lemmas2.agda lemmas3.agda lemmas4.agda proofs.agda
OBJ=$(SRC:.agda=.agdai)


all: proofs.agdai


%.agdai: %.agda
	$(AGDA) $(FLAGS) $^


clean:
	rm -f $(OBJ) *~
