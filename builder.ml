(* Question1 *)

type string_builder = Feuille of int*string | Noeud of int*string_builder*string_builder ;;

(*@requires un string_builder
  @ensures retourne la longueur de caractère dans string_builder
*)
let length sb = match sb with
  |Noeud(a,_,_)->a
  |Feuille(a,_)->a;;
  
(*@requires string
  @return la feuille de string.
*)
let word str = Feuille (String.length(str),str);;

(*@requires 2 string_builder
  @ensures retourne le nouveau string_builder concaténé.
*)
let concat sb1 sb2 = let length (sb1,sb2)=match (sb1,sb2) with 
  |(Noeud(a,_,_),Noeud(b,_,_))->a+b
  |(Feuille(a,_),Noeud(b,_,_))->a+b
  |(Noeud(a,_,_),Feuille(b,_))->a+b
  |(Feuille(a,_),Feuille(b,_))->a+b
                     in Noeud(length (sb1,sb2),sb1,sb2);;

(* Question 2 *)

(*@requires string_builder qui est une racine pour un mot.
  @ensures retourn la liste des partitions de mot (a l'ordre)    
*)
let rec getStr = function 
  |Feuille (a,sb)-> [(sb)]
  |Noeud(a,sb1,sb2)-> (getStr sb1)@(getStr sb2);; 

(*@requires n:l'index pour un caractère d'une chaîne et une racine pour un mot.
  @ensuires retourne un caractère dans la chaîne d'après sa position dans l'index;   
*)
let char_at index sb = if ((index+1) <= (length sb)) then String.get (String.concat "" (getStr sb)) index
else failwith "Index > length !";;  

  
(* Question 3 *)

(*@requires 2 entiers i et m , 1 string_builder .
  @ensures les caractères dans le string que le string_builder représente (dès i à i+m)  
*)
let rec sub_string i m sb = 
  if (0<=i)&&(i<i+m)&&(i+m<=(length sb))	
  then match sb with
    |Feuille(nb,str)-> word (String.sub str i m)
    |Noeud(nb,sb1,sb2)->if(i>=(length sb1)) then sub_string (i-(length sb1)) m sb2
    else if(i+m)<=(length sb1) then sub_string i m sb1 
    else concat (sub_string i ((length sb1)-i) sb1) (sub_string 0 ((i+m)-(length sb1)) sb2) 
 else
   failwith "Wrong input";;


(* Question 4 *)

(*@requires string_builder  
  @ensures retourne le coût de string_builder 
*)  
let cost sb =
  let rec costn (n,sb) =  match (n,sb) with 
  |(n,Feuille(nb,_)) -> n*nb
  |(n,Noeud(nb,left,right)) -> (costn (n+1,left)) + (costn (n+1,right)) 
   in     costn (0,sb);;


(* Question 5 *)

(*@retourne le code ASCII de chiffre
  @ensures retourne le char qui correspond le code ASCII
*)
let int_to_char num = 
  if((num >= 0)&&(num<=57)) then 
    Char.chr (num+65)
  else failwith"Input : number in range(0,57) required";;

(*@requires rien
  @ensures retourne un chiffre aléatoire entre 1~5
*)
let randTaille()=(Random.int 5)+1;;  

(*@requires rien
  @ensures retourne le caractère associé au code ASCII
*)
let randChar()= Char.escaped (int_to_char(Random.int 57));;

(*@requires rien
  @ensures retourne un string aléatoire avec la taille 1～５ 
*)
let randStr() =let rec randCharList n = match n with 
  |0 ->[]  
  |_ -> randChar()::(randCharList (n-1))
 in 		String.concat "" (randCharList (randTaille()));;

(*@requires rien
  @ensures retourne un chiffre par hasard entre 1~２
*)
let leftOrRight() = (Random.int 2)+1;; 

(*@requires int i
  @ensures retourne un string_builder de profondeur i
*)
let rec random_string (i) = let x=leftOrRight() in match i with
  | 0-> word (randStr())
  | n-> if x=1 then concat (random_string (n-1)) (word (randStr()))
  else concat (word (randStr())) (random_string (n-1));;
 
 
(* Question 6 *)

(*@requires string_builder qui est une racine pour un mot.
  @ensures retourne la liste des partitions du mot dans l'ordre   
*)
let rec list_of_string = function 
  |Feuille (a,sb)-> [(sb)]
  |Noeud(a,sb1,sb2)-> (getStr sb1)@(getStr sb2);; 


(* Question 7 *)

(*@requires string_builder 
  @ensures retourne la liste de Feuille
*)
let rec getFlist = function 
  |Feuille (a,sb)-> [Feuille (a,sb)]
  |Noeud(a,sb1,sb2)-> (getFlist sb1) @ (getFlist sb2);; 

(*@requires 2 string_builder 
  @ensures calcule le coût après leur concaténation 
*)
let cosAfterCon sb1 sb2 =cost (concat sb1 sb2);;

(*@requires 2 string_builder 
  @ensures calcule le coût plus faible dans la liste
*)
let rec getCostMin1 n list = 
  match list with
  |[]-> 0
  |t::[]-> n
  |t::b::q-> if (n)>(cosAfterCon t b) then getCostMin1 (cosAfterCon t b) (b::q) 
  else getCostMin1 n (b::q) ;;

(*@requires liste de feuilles 
  @ensures retourne le coût des deux premières feuilles
*)
let getCostFirst list = match list with
  |[]->failwith "Wrong input"
  |t::[]->failwith "Wrong input"
  |t::b::q->cosAfterCon t b;;

(*@requires liste de feuilles 
  @esnures retourne la liste qui a concaténé les deux feuilles successifs dont la concaténation a le coût le plus faible.
*)
let rec concatMin list = let costMin list = getCostMin1 (getCostFirst list) list in
  let min=costMin list in
   match list with
     |[]->failwith "Wrong"
     |t::[]->failwith "Wrong"
     |t::b::q->if (cosAfterCon t b)=min then (concat t b)::q
     else t::(concatMin (b::q));;   
        
(*@requires string_builder
 @ensures retourne string_builder optimisé
*)    
let balance ab =let rec balanceL list  = match list with
  |[]->failwith "Wrong input"
  |t::[]->failwith "Wrong input"
  |t::q::[]-> [(concat t q)]
  |t::b::q ->balanceL (concatMin (t::b::q))
 in
   match balanceL (getFlist ab) with
  |[]->failwith "Wrong"
  |q::t->q;;

(* Question8 *)

(*@requires rien
  @ensures retourne la profondeur d'arbre entre 1~5;
*)  
let ranDeep()=(Random.int 5)+1;;

(*@requires rien
  @ensures retourne un arbre aléatoire (profondeur entre 1~5);
*)  
let ranDeepAB() = random_string (ranDeep());;

(*@requires n est le nombre d'échantillons 
  @ensures la liste d'échantillons ;
*)   
let rec echantillon (n) = match n with
  |0->failwith "No tree"
  |1-> let ab = ranDeepAB() in [(cost ab)-(cost (balance ab))]
  |n-> let ab = ranDeepAB() in [(cost ab)-(cost (balance ab))]@(echantillon (n-1));;

(*@requires list 
  @ensures retourne le max de la liste
*)   
let rec max_number l =
    match l with 
    |[] -> failwith"Empty list"
    |x::[] -> x
    |x::xs -> max x (max_number xs);;

(*@requires list 
  @ensures retourne le min de la liste
*)  
let rec min_number l =
    match l with 
    |[] -> failwith"Empty list"
    |x::[] -> x
    |x::xs -> min x (max_number xs);;

(*@requires list 
  @return la moyenne de la liste. 
*)  
let moyenne l = let rec somme (count,sum,l) = match l with 
  |[]->failwith"Empty list"
  |t::[]-> (count+1,sum+t,[])
  |t::q -> somme (count+1,sum+t,q) in
  let (count,sum,l)=somme (0,0,l) in float_of_int(sum)/. float_of_int(count);;

(*@requires list  
  @ensures retourne la médiane de la liste  
*)  
let mediane liste =
  let l = List.sort compare liste in
  List.nth l (((List.length liste)-1)/2)
;;


(*@requires le nombre d'échantillons   
  @ensures retourne le min, le max, la moyenne et la valeur médiane en analysant les gains par la fonction 'balance' 
*)  
let analyse (n) = let e = echantillon (n) in (min_number(e),max_number(e),moyenne(e),mediane(e));;
let min,max,moy,med = analyse(1000);;

print_string "min cost=";;
print_int(min);;
print_newline();;

print_string "max cost=";;
print_int(max);;
print_newline();;

print_string "avg cost=";;
print_float(moy);;
print_newline();;

print_string "med cost=";;
print_int(med);;
print_newline();;

print_string "Access costs for n=1000 \n"

(*TESTS*)

let exemple = Noeud(7,Feuille(1,"G"),Noeud(6,Feuille(3,"ATT"),Noeud(3,Feuille(1,"A"),Feuille(2,"CA"))));;

let cas = Noeud(6,Noeud(3,Feuille(1,"A"),Noeud(2,Feuille(1,"A"),Feuille(1,"A"))),Feuille(3,"ATT"));;

let test = Noeud (13,Noeud (7, Feuille (1, "G"),Noeud (6, Feuille (3, "ATT"),Noeud (3, Feuille (1, "A"), Feuille (2, "CA")))),Noeud (6,Noeud (3, Feuille (1, "A"),
Noeud (2, Feuille (1, "A"), Feuille (1, "A"))),Feuille (3, "ATT")));;

let () = assert ( length exemple = 7 );;

let () = assert ( word "exemple" = Feuille(7,"exemple"));;

let () = assert ( concat exemple cas = test);;

let () = assert ( char_at 3 exemple = 'T');;

let () = assert ( sub_string 1 2 exemple = Feuille (2, "AT"));;

let () = assert ( cost exemple = 16);;

let () = assert ( random_string 4 != random_string 4);;

let () = assert ( list_of_string exemple = ["G"; "ATT"; "A"; "CA"]);;

(* cas non optimal pour balance*)
let () = assert ( balance exemple = Noeud(7,Noeud(4,Feuille(1,"G"),Feuille(3,"ATT")),Noeud(3,Feuille(1,"A"),Feuille(2,"CA"))));;

let () = assert ( List.length( echantillon 10) = 10);;
let () = assert ( echantillon 10 != echantillon 10);;

let l = [1; 3; 5; 7; 9];;

(* ne marche pas pour les négatifs*)
let () = assert ( min_number l = 1);;
let () = assert ( max_number l = 9);;
let () = assert ( moyenne l = 5.);;
let () = assert ( mediane l = 5);;
