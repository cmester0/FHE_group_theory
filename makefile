run:
	ghc --make *.hs -O3 -fexpose-all-unfoldings -fasm -fforce-recomp -v0  -funbox-strict-fields -optc-O3 -optc-march=core2 -auto-all -caf-all -freverse-errors -msse4.2 -Rghc-timing
	./examples

clean:
	rm *.hi
	rm examples
	rm *.o
