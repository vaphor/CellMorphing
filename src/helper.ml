module SMap = Map.Make( String )

(*Returns the printing of each element of a list with a seperator in between each element*)
let rec printList printFunc l separator=
  match l with
  | [] -> ""
  | [a] -> printFunc a
  | a::q -> (printFunc a) ^ separator ^ (printList printFunc q separator)

(*Prints all values of a map with a seperator between each element*)
let printMap printFunc m seperator=
  let l = SMap.bindings m in
  printList (fun (k, v) -> printFunc v) l seperator

(*Adds a new item in the map, fails if the key already exists in the map*)
let add_unique map key value =
  if SMap.exists (fun k v -> k=key) map then failwith (Printf.sprintf "Key %s already in map" key);
  SMap.add key value map

(*Return all keys of the map*)
let getKeys map =
  List.map fst (SMap.bindings map)

(*Creates the list [f(0); f(1); ...; f(n-1)]*)
let rec listCreate f n = 
  match n with
  | k when k<=0 -> []
  | k -> (listCreate f (k-1)) @ [f (k-1)]

(*Removes the element at position i (starting at 0) in the list*)
let rec listRemove l i =
  match l,i with
  | [],i -> []
  | a::q, 0 -> q
  | a::q, _ -> a::(listRemove q (i-1))

(*Inserts an element in the list. The new element's position is i*)
let rec listInsert l elem i =
  match l,i with
  | _, i when i < 0 -> failwith "Inserting at negative index"
  | _,0 -> elem::l
  | a::q, i -> a::(listInsert q elem (i-1))
  | [], i -> failwith "Inserting at too big index"

(*Returns the first word of a string*)
let firstWord str =
  let rec recAdd i =
    if String.length str <= i then String.sub str 0 i
    else begin
      let c = String.get str i in
      if c  <> ' ' then recAdd (i+1)
      else String.sub str 0 i
    end in
  recAdd 0








