Z3CONFIG=

Arsenic : *.ml *.mly *.mll
	ocamlbuild -yaccflag -v -lib `pwd`/z3/build/api/ml/z3 -lflags -ccopt,-L`pwd`/z3/build/api/ml -lib unix -lib str arsenic.native
#	ocamlbuild -yaccflag -v -lib unix -lib str arsenic.native

Check : *.ml *.mly *.mll
	ocamlbuild -yaccflag -v -lib `pwd`/z3/build/api/ml/z3 -lflags -ccopt,-L`pwd`/z3/build/api/ml -lib unix -lib str checkquery.native

ToLaTeX : *.ml *.mly *.mll
	ocamlbuild -yaccflag -v -lib `pwd`/z3/build/api/ml/z3 -lflags -ccopt,-L`pwd`/z3/build/api/ml -lib unix -lib str tolatex.native

Test : *.ml *.mly *.mll
	ocamlbuild -yaccflag -v -lib unix -lib str tester.native

newz3 : 
	cd z3; git clone https://git.codeplex.com/forks/jjb/z3
	cd z3; rm -fr build; ./configure $(Z3CONFIG)
	cd z3/build; make -j4
	cd z3/build; sudo make install PREFIX=/usr
	cd z3; rm -fr build/api/ml; mkdir build/api/ml
	cd z3; cp src/api/ml/Makefile.build build/api/ml/Makefile
	cd z3/build/api/ml; make z3.cma z3.cmxa

clean :
	rm -fr _build *.native; \
	rm -f z3.mli Arsenic Check ToLateX Test

links:;\
	rm -f z3.mli Arsenic Check ToLaTeX Test; \
	ln -s z3/build/api/ml/z3.mli; \
	chmod -w z3.mli; \
	ln -s arsenic.native Arsenic; \
	ln -s checkquery.native Check; \
	ln -s tolatex.native ToLaTeX; \
	ln -s tester.native Test

simpletest:
	./Test proofs/MP.proof
	./Test proofs/MP_loparallel.unproof -error 5 lo-parallel -error 6 lo-parallel -error 5 bo-parallel -error 8 "EXT stability"
	./Test proofs/MP_loparallelB.unproof -error 5 lo-parallel -error 6 lo-parallel -error 5 bo-parallel
	./Test proofs/MP_loparallelC.unproof -error 8 "EXT stability of f=1=>m=0 against _B(m=0) | m := 1" \
										 -error 8 "EXT stability of f=1=>m=0 against _B(f=0) | f := 1" \
										 -error 9 "EXT stability of r1=1=>f=1/\m=0 against _B(m=0) | m := 1"
	./Test proofs/MP_boparallel.unproof -error 5 bo-parallel -error 8 "EXT stability"
	./Test proofs/MP_boparallelB.unproof -error 5 bo-parallel
	./Test proofs/MP_boparallelC.unproof -error 10 "EXT stability"
	./Test proofs/almostWRC.proof
	./Test proofs/almostISA2.proof
	./Test proofs/WRC.proof
	./Test proofs/MP_conditional.proof
	./Test proofs/PPOCA.unproof -error 20 "inheritance of embroidery r3=1"
	./Test -LocalSpec true proofs/PPOCAgo.unproof -error 16 "inheritance of embroidery m=1"
	./Test -LocalSpec false proofs/PPOCAgo.unproof -error 15 inclusion -error 16 "inheritance of embroidery m=1"
	./Test proofs/PPOCA.proof
	./Test proofs/MP_dountil.proof
	./Test proofs/MP_dountil_locd.proof
	./Test proofs/MP_while.proof
	./Test proofs/LB.proof
	./Test -SCloc false proofs/LB.proof -error 9 "EXT stability" -error 16 "EXT stability"
	./Test -SCreg true proofs/SCreg.proof
	./Test -SCreg false proofs/SCreg.proof -error 6 lo-parallel
	./Test -SCreg true proofs/nothinair.proof
	./Test -SCreg false proofs/nothinair.proof
	./Test -LocalSpec true proofs/C11_42.proof
	./Test -LocalSpec false proofs/C11_42.proof -error 17 lo-parallel \
	                                            -error 18 lo-parallel -error 20 inclusion \
	                                            -error 22 "inheritance of embroidery false"
	./Test proofs/SB2.proof
	./Test proofs/IRIW.proof
	./Test proofs/UEXT.unproof -error 7 "UO-EXT stability"
	./Test proofs/uo-unstable-interference.unproof -error 4 "self-uo stability"
	./Test -SCloc false proofs/LBwithoutSCloc.proof
	./Test -SCloc false -sat false proofs/LBwithoutSCloc.proof
	./Test proofs/tokenringsingleassert.proof
	./Test proofs/tokenringsingleifthen.proof
	./Test proofs/tokenringsingleifthenaux.proof
	./Test proofs/tokenring3assert.proof
	./Test proofs/tokenring3ifthen.proof

coherencetest:
	./Test proofs/CoRR0.proof
	./Test proofs/CoRR1.proof
	./Test proofs/CoRR2.proof
	./Test -SCloc false proofs/CoRR2.proof -error 0 "coherence assertions" \
										   -error 11 "inheritance of embroidery r1!=r2=>_c(x,r1,r2)" \
										   -error 15 "inheritance of embroidery r1!=r2=>_c(x,r1,r2)"
	./Test proofs/CoRR2_aux.proof
	./Test -SCloc false proofs/CoRR2_aux.proof 
	./Test proofs/CoWW.proof
	./Test proofs/S.proof
	./Test proofs/S_simple.proof
	./Test proofs/WWC.proof
	./Test proofs/R.proof
	./Test proofs/R+bo+lo.unproof -undecided 15 "inheritance of program postcondition"
	./Test proofs/R+uo+lo.unproof -error 15 "inheritance of program postcondition"
	./Test proofs/R+uo+lo+flag.unproof -error 15 "EXT stability of f=1=>(_U(x=1) since y=1)" \
									   -error 16 "EXT stability of r2=1\/f=1=>(_U(x=1) since y=1)"
	./Test proofs/R+uo+lo+flag.unparse -error 3 "_B(_U(x=1) since y=1) contains temporal coincidence" \
									   -error 8 "_B(_U(x=1) since y=1) contains temporal coincidence"
	./Test proofs/R+uo+lo+otherflag.unproof -error 8 "EXT stability of f=1=>ouat(x=0/\y=2)"
	./Test proofs/R+uo+lo+otherflag.unparse -error 14 "_B(ouat(x=0/\y=2)) contains temporal coincidence" \
											-error 20 "_B(ouat(x=0/\y=2)) contains temporal coincidence"
	./Test -spunchanged false proofs/R+uo+lo.unproof -error 15 "inheritance of program postcondition" \
													 -error 13 "EXT stability of r1=0=>ouat(x=0/\y=2) against true | x := 1"
	./Test proofs/WRW+WR.proof
	./Test proofs/IRRWIW.proof
	./Test proofs/WRR+2W.proof
	./Test proofs/IRRWIW.proof

	./Test proofs/2+2W.proof
	# ./Arsenic proofs/WRW+2W.proof
	./Test -SCloc false -sat false proofs/nonSCloctermination.proof
	./Test proofs/SClocnontermination.proof
