all: project

# These must be in the right order--no forward refs
FILES = decisiontree.ml hashtable.ml main.ml

project: $(FILES)
	ocamlc -g -o project unix.cma str.cma $(FILES)

clean: 
	rm -f project *.cmi *.cmo
