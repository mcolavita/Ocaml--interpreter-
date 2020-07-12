(*Definizione della grammatica del dizionario*)
type ide = string;;
type exp = 
  | Eint of int 
  | Ebool of bool 
  | Estring of string
  | Den of ide 
  | Prod of exp * exp 
  | Sum of exp * exp 
  | Diff of exp * exp 
  | Eq of exp * exp 
  | Minus of exp 
  | IsZero of exp 
  | Or of exp * exp 
  | And of exp * exp 
  | Not of exp 
  | Ifthenelse of exp * exp * exp 
  | Let of ide * exp * exp 
  | Fun of ide * exp 
  | FunCall of exp * exp 
  | Letrec of ide * exp * exp

  (*Dizionario*)

  |Dict of (ide * exp) list
  |Insert of ide * exp * exp (*Insert(key,value,dict)*)
  |Delete of ide * exp (*Delete magazzino(key,dict)*)
  |HasKey of ide * exp (*Haskey magazzino(key,dict)*)
  |Iterate of exp * exp (*function,dict*)
  |Fold of exp * exp
  |Filter of ide list * exp (*key list,dict*)
  ;;

  
(*ambiente polimorfo*)
(*r ambiente , i identificatore, v valore*)
type 't env = ide -> 't;;
let emptyenv (v : 't) = function x -> v;;
let applyenv (r : 't env) (i : ide) = r i;;
let bind (r : 't env) (i : ide) (v : 't) = function x -> if x = i then v else applyenv r x;;  


(*Valori esprimibili*)
type evT =
  | Int of int 
  | Bool of bool
  | Unbound
  | String of string
  | FunVal of evFun
  | RecFunVal of ide * evFun
  | DictVal of (ide * evT) list
  and evFun = ide* exp * evT env;;


(*type checking*)
let typecheck (s : string) (v : evT) : bool = match s with
  |"int" -> (match v with
    |Int(_)-> true
    |_ -> false)
  |"string" -> (match v with
    |String(_) -> true
    |_ -> false)
  |"bool" -> (match v with
   |Bool(_) -> true
   |_ -> false)
  |"dict" -> (match v with
    |DictVal(_) -> true
    |_ -> false)
  | _ -> failwith("Non è un tipo valido");;


(* Funzioni primitive *)
let sum x y = if (typecheck "int" x) && (typecheck "int" y)
    then (match (x,y) with
        | (Int(n), Int(u)) -> Int(n + u)
        | _ -> failwith("Errore durante l'applicazione di <sum>"))
    else failwith("<sum> errore di tipo")
;;

let diff x y = if (typecheck "int" x) && (typecheck "int" y)
    then (match (x,y) with
        | (Int(n), Int(u)) -> Int(n - u)
        | _ -> failwith("Errore durante l'applicazione di <diff>"))
    else failwith("<diff> errore di tipo")
;;

let prod x y = if (typecheck "int" x) && (typecheck "int" y)
    then (match (x,y) with
        | (Int(n), Int(u)) -> Int(n * u)
        | _ -> failwith("Errore durante l'applicazione di <prod>"))
    else failwith("<prod> errore di tipo")
;;

let eq x y = if (typecheck "int" x) && (typecheck "int" y)
    then (match (x,y) with
        | (Int(n), Int(u)) -> Bool(n = u)
        | _ -> failwith("Errore durante l'applicazione di <eq>"))
    else failwith("<eq> errore di tipo")
;;

let vel x y = if (typecheck "bool" x) && (typecheck "bool" y)
    then (match (x,y) with
        | (Bool(b), Bool(e)) -> Bool(b || e)
        | _ -> failwith("Errore durante l'applicazione di <vel>"))
    else failwith("<vel> errore di tipo")
;;



let et x y = if (typecheck "bool" x) && (typecheck "bool" y)
    then (match (x,y) with
        | (Bool(b), Bool(e)) -> Bool(b && e)
        | _ -> failwith("Errore durante l'applicazione di <et>"))
    else failwith("<et> errore di tipo")
;;

let minus x = if (typecheck "int" x)
    then (match x with
        | Int(n) -> Int(-n)
        | _ -> failwith("Errore durante l'applicazione di <minus>"))
    else failwith("<minus> errore di tipo")
;;

let iszero x = if (typecheck "int" x)
    then (match x with
        | Int(n) -> Bool(n=0)
        | _ -> failwith("Errore durante l'applicazione di <iszero>"))
    else failwith("<iszero> errore di tipo")
;;

let non x = if (typecheck "bool" x)
    then (match x with
        | Bool(true)  -> Bool(false)
        | Bool(false) -> Bool(true)
        | _ -> failwith("<non> errore di tipo"))
    else failwith("<non> errore di tipo")
;;

(*Funzione che mi permette di controllare se un elemento fa parte della lista*)
let rec exists (k : ide ) (l : ide list) : bool = match l with
    []->false
    |z::zs -> if (k=z) then true else exists k zs;;


(*interprete*)
let rec eval (e : exp) (r : evT env) : evT = match e with
	| Eint n -> Int n 
    | Ebool b -> Bool b 
    | Estring s -> String s
	| IsZero a -> iszero (eval a r) 
	| Den i -> applyenv r i 
	| Eq(a, b) -> eq (eval a r) (eval b r) 
	| Prod(a, b) -> prod (eval a r) (eval b r) 
	| Sum(a, b) -> sum (eval a r) (eval b r) 
	| Diff(a, b) -> diff (eval a r) (eval b r) 
	| Minus a -> minus (eval a r) 
	| And(a, b) -> et (eval a r) (eval b r) 
	| Or(a, b) -> vel (eval a r) (eval b r) 
	| Not a -> non (eval a r) 
	| Ifthenelse(a, b, c) -> 
		let g = (eval a r) in
			if (typecheck "bool" g) 
				then (if g = Bool(true) then (eval b r) else (eval c r))
				else failwith ("nonboolean guard") 
	| Let(i, e1, e2) -> eval e2 (bind r i (eval e1 r)) 
	| Fun(i, a) -> FunVal(i, a, r) 
	| FunCall(f, eArg) -> 
		let fClosure = (eval f r) in
			(match fClosure with
				|FunVal(arg, fBody, fDecEnv) -> eval fBody (bind fDecEnv arg (eval eArg r)) 
				|RecFunVal(g, (arg, fBody, fDecEnv)) -> 
					let aVal = (eval eArg r) in
						let rEnv = (bind fDecEnv g fClosure) in
							let aEnv = (bind rEnv arg aVal) in
								eval fBody aEnv 
				| _ -> failwith("non functional value")) 
    | Letrec(f, funDef, letBody) ->
        		(match funDef with
            		| Fun(i, fBody) -> let r1 = (bind r f (RecFunVal(f, (i, fBody, r)))) in
                         			                eval letBody r1 
                    | _ -> failwith("non functional def"))
                    
                    
    (*Dizionario*)                  
                    
                    
    | Dict(dictlist) -> DictVal(evalList dictlist r)

    |Insert(name,expToAdd,dictlist) ->
        let v1= eval expToAdd r in 
            let v2 = eval dictlist r in
                (match v2 with
                    DictVal(dict)-> if (checkKey dict name) then failwith("Chiave già presente") else  DictVal(add dict name v1)
                    |_ -> failwith("Argomento non corretto"))

   
    |Delete(name,dictlist)->
        let v1 = eval dictlist r in
            (match v1 with
                DictVal(dict) -> if (checkKey dict name) then DictVal(remove dict name) else failwith("Chiave non esistente")
                |_ -> failwith("Argomento non corretto"))
     


    |HasKey(name,dictlist) ->
        let v1 = eval dictlist r in
            (match v1 with
                DictVal(dict) -> Bool(checkKey dict name)
                | _ -> failwith ("Argomento non corretto"))

    |Iterate(f,dictlist) ->
        let fClosure = eval f r in 
            (match (fClosure,eval dictlist r) with 
            
                (FunVal(arg,fBody,fEnv),DictVal(dict)) -> DictVal(apply arg fBody fEnv dict)
                |(RecFunVal(g,(arg,fBody,fEnv)),DictVal(dict))-> DictVal( applyRec arg fBody fEnv dict g fClosure)
                |(_,_)-> failwith("Espressione errata: Fun, dizionario richiesto"))
            

     | Fold(funct, dict) ->
        (match eval funct r, dict with
            | FunVal(_, _, _), Dict (v) ->
                let rec fold (f : exp) (dict : (ide * exp) list) (acc : evT) (r : evT env) : evT =
                    match dict with
                    | [] -> acc
                    | (_, v1)::t -> match acc, (eval (FunCall(f, v1)) r) with
                                    | (Int(u), Int(v)) -> fold f t (Int(u+v)) r
                                    | _ -> failwith("error in applying function")
                    in fold funct v (Int(0)) r
            | _ -> failwith("not a dictionary"))


    
            
    |Filter(keyList,dictlist) ->
        let v1 = eval dictlist r in 
            (match v1 with
            DictVal(dict) -> DictVal(filter keyList dict)
            |_ -> failwith("Argomento non corretto"))




    and evalList (l :(ide * exp ) list ) (env : evT env)  : (ide * evT) list = match l with
            []-> []
            |(ide,v)::xs -> (ide, eval v env)::(evalList xs env)

    and add (l: (ide * evT) list) (name : ide) (value: evT) : (ide * evT) list = match l with

            []-> (name,value)::[]
            |(ide,v)::xs ->  (ide,v)::(add xs name value) 

    and checkKey (l: (ide *evT)list) (name: ide) : bool = match l with
                []-> false
                |(key,value)::xs -> if (name = key) then true else checkKey xs name


    and remove (l: (ide * evT) list) (name: ide) : (ide * evT) list = match l with
                []->[]
                |(key,value)::xs -> if(key = name ) then xs else (key,value)::remove  xs name
    
    and apply (arg : ide) (body : exp) (env : evT env) (l : (ide * evT) list) : (ide * evT) list = 
		match l with
		[] -> []
		|(ide,v)::xs -> 
			let env1 = bind env arg v in
			try (ide,eval body env1)::(apply arg body env xs)
				with 
                Failure explanation -> (ide,v)::(apply arg body env xs)
                
    and applyRec (arg : ide) (body : exp) (env : evT env) (l : (ide * evT) list) (g : ide) (f : evT) : (ide * evT) list =
		match l with
		[] -> []
		|(ide,v)::xs -> 
			let rEnv = bind env g f in
				let aEnv = bind rEnv arg v in
					try (ide,eval body aEnv)::(applyRec arg body env xs g f)
						with
                        Failure explanation -> (ide,v)::(applyRec arg body env xs g f)




    and filter (keyList : ide list) (l : (ide * evT) list) : (ide * evT) list = match l with
                    [] -> []
                    |(k,v)::ks -> if (exists k keyList) then (k,v)::(filter keyList ks)
                                  else filter keyList ks

    ;;
    (*Test*)
    

    let env0 = emptyenv Unbound;;
  

    (*Dichiarazione dizionari*)


    let emptyDict = Dict [];;
    eval emptyDict env0;; (*Risultato atteso:  Dict[]*)

    (*Dizionario con inserimento di elementi*)
    let dict1 = Dict([
        ("mele",   Eint(430));
        ("banane", Eint(312));
        ("arance", Eint(525));
        ("pere",   Eint(217))
    ]);;
    eval dict1 env0;;
    (*Risultato atteso : Dict[("mele",430);("banane",312);("arance",525);("pere",217)]*)
    
    (*Inserimento chiave kiwi non presente*)

    let dict2 = Insert("kiwi",Eint(300),dict1);;
    eval dict2 env0;;
    (*Risultato atteso : Dict[("mele",430);("banane",312);("arance",525);("pere",217);("kiwi",300)]*)

    (*Inserimento chiave già esistente "mele"*)
    try eval (Insert("mele", Eint(550), dict2)) env0
    with Failure(msg) -> Printf.printf "Insert, chiave esistente: OK (%s)\n" msg; DictVal([]);;
    (*Risultato atteso: chiave già inserita*)

    (*Rimozione chiave "banane" esistente*)
    let dict3 = Delete("banane",dict2);;
    eval dict3 env0;;
    (*Risultato atteso : Dict[("mele",430);("arance",525);("pere",217);("kiwi",300)]*)
    
    (*Controllo se la chiave "arance" è presente nel dizionario*)
    let dict4 = HasKey("arance",dict3);;
    eval dict4 env0;; (*Bool- true*)

    (*Controllo se la chiave peperoni è presente nel dizionario*)
    let dict5 = HasKey("peperoni",dict3);;
    eval dict5 env0;; (*Bool- false*)


    (*Funzione che mi incrementa di 1 i valori delle chiavi del dizionario*)
    let dict6 = Iterate(Fun("y",Sum(Den "y", Eint 1)),dict3);;
    eval dict6 env0;; (*Restituisce i risultati incrementati di 1*)
    (*Risultato atteso : Dict[("mele",431);("arance",526);("pere",218);("kiwi",301)]*)


    (*Fold, funzione somma 0*)
    let dict7 = Fold(Fun("y", Sum(Den "y", Eint 0)), dict1);;
    eval dict7 env0;;
    (*Risultato atteso: 1484*)

    (*Fold funzione somma 5*)
    let dict8 = Fold(Fun("y", Sum(Den "y", Eint 5)), dict1);;
    eval dict8 env0;;
    (*Risultato atteso: 1504*)

    (*Filter su dict1*)
    let dict9 = Filter(["mele";"pere"],dict1);;
    eval dict9 env0;;
    (*Risultato atteso : Dict[("mele",431);("pere",218)]*)

    (*Filter su dict1, lista vuota*)
    let dict10 = Filter([],dict1);;
    eval dict10 env0;;
     (*Risultato atteso : Dict[]*)



