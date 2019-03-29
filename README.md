# Rely-Guarantee
Coq development of Rely-Guarantee method

coq version 8.8.0

Rely-Guarantee method proposed by C.B.Jones in 1981 based on Hoare-Logic is a useful method to construct compositional verification for shared variable concurrency programs. This project implements the method and its corresponding program logic with the soundness proof using coq proof assistant according to the attached paper. The language we use is based on an imperative language called IMP defined in "Software Foundations". We add a parallel command to the language for concurrency. The syntax and smallstep semantics of the language are defined in Imp.v. RelyGuarantee.v implements Rely-Guarantee method and the corresponding program logic as well as its soundness proof. Note that we do not implement the last rule of the program logic - the auxiliary rule with no harm to soundness and completeness of the program logic.
