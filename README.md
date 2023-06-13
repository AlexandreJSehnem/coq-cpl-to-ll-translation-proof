# coq-cpl-to-ll-translation-proof
 Formalizing the translation from classical propositional logic to linear logic in coq
 
------- Como compilar --------

Atualmente é necessario:

- Instalar Nanoyalla: para isso é só seguir os passos descritos no "Yalla-free Installation" dentro do readme da pasta nanoyalla.

- Compilar a_base.v, usando os seguintes comandos:

    $ coq_makefile -f _CoqProject -o CoqMakefile
    
    $ make all -f CoqMakefile
