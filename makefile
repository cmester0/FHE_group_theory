run:
	ghc --make *.hs -O2 -fexpose-all-unfoldings -fasm -fforce-recomp -v0  -funbox-strict-fields -optc-O3 -optc-march=core2 -auto-all -caf-all
	./examples

run_group:
	ghc coxeter.hs
	./coxeter

run_opt:
	ghc -optc-O3 fhe.hs
	./fhe
