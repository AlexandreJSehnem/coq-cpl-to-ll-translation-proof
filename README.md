# coq-cpl-to-ll-translation-proof
 Formalizing the translation from classical propositional logic to linear logic in coq
 
------- Como compilar --------

Atualmente é necessario:

- Instalar Nanoyalla: para isso é só seguir os passos descritos no "Yalla-free Installation" dentro do readme da pasta nanoyalla.

- Compilar a_base.v, usando os seguintes comandos:

    $ coq_makefile -f _CoqProject -o CoqMakefile
    
    $ make all -f CoqMakefile
	
	
------ Notas sobre a tradução ------
- A dedução natural da lógica proposicional clássica é um tipo indutivo chamado Nc:

- cpl_to_ll: Esse fixpoint possui as regras de tradução LPC -> LL, para cada um dos conectivos da lógica clássica.
	A	=> ?!(At) -> quando A for axioma
	
	A ∨ B	=> (At) ⅋ (Bt)
	
	A -> B 	=> (?(At)^) ⅋ (Bt)
	
	~A	=> ?(At)^
	
	bot	=> zero
	
	A ∧ B	=> ?(((?((At)^)) ⅋ (?((Bt)^)))^)

- dual_set_cpl_to_ll: A biblioteca nanoyalla só possui implementação para as regras dos sequentes da direita, então este fixpoint é utilizado para fazer uma tradução LPC -> LL e ao mesmo também fazer o dual de todas as regras para que elas possam ser usadas do lado direito do sequente.

	LPC		LL
	
	(A |- B)	|- (dual_set_cpl_to_ll A), (cpl_to_ll B)

