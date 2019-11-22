run:
	ghc fhe.hs
	./fhe

run_group:
	ghc coxeter.hs
	./coxeter

run_opt:
	ghc -optc-O3 fhe.hs
	./fhe
