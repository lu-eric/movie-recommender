exception ImplementMe
exception Impossible
exception Feature
exception MyError of int

(* branches of decision tree *)
(*type attribute = int*)
(* contains the question at each node of the tree *)
type question = int
(* genre is implemented as an integer *)
type genre = int
type attribute = genre

(*===================================================*)
(* Order Code from Moogle Pset *)
(* The type order is used for comparison operations *)
type order = Less | Eq | Greater ;;

let string_compare x y = 
  let i = String.compare x y in
    if i = 0 then Eq else if i < 0 then Less else Greater ;;

let int_compare x y = 
  let i = x - y in 
    if i = 0 then Eq else if i < 0 then Less else Greater ;;
(*=============================================================*)

let att_compare (x: attribute) (y: attribute) =
  let i = x - y in
  if i = 0 then Eq else if i < 0 then Less else Greater ;;

(******************************************************************************)
(* BT DICT CODE from moogle pset (written by Stewart Richardson) *)
module type DICT = 
sig
  type key   
  type value 
  type dict

  (* An empty dictionary *)
  val empty : dict 

  (* Reduce the dictionary using the provided function f and base case u. 
   * Our reducing function f must have the type:
   *      key -> value -> 'a -> 'a
   * and our base case u has type 'a.
   * 
   * If our dictionary is the (key,value) pairs (in any order)
   *      (k1,v1), (k2,v2), (k3,v3), ... (kn,vn)
   * then fold should return:
   *      f k1 v1 (f k2 v2 (f k3 v3 (f ... (f kn vn u))))
   *)
  val fold : (key -> value -> 'a -> 'a) -> 'a -> dict -> 'a

  (* Returns as an option the value associated with the provided key. If
   * the key is not in the dictionary, return None. *)
  val lookup : dict -> key -> value option

  (* Returns true if and only if the key is in the dictionary. *)
  val member : dict -> key -> bool

  (* Inserts a (key,value) pair into our dictionary. If the key is already
   * in our dictionary, update the key to have the new value. *)
  val insert : dict -> key -> value -> dict

  (* Removes the given key from the dictionary. If the key is not present,
   * Return the original dictionary. *)
  val remove : dict -> key -> dict

  (* Return an arbitrary key, value pair along with a new dict with that
   * pair removed. Return None if the input dict is empty *)
  val choose : dict -> (key * value * dict) option

  (* similar to lookup, but also returns the key *)
  val fast_lookup : dict -> key -> (key * value) option

  (* finds size of the dictionary *)
  val length : dict -> int

end

(* Argument module signature to our DICT functors *)
module type DICT_ARG =
sig
  type key
  type value
  val compare : key -> key -> order
end

module BTDict(D:DICT_ARG) : (DICT with type key = D.key
with type value = D.value) =
struct

  exception TODO
  exception TEST

  type key = D.key
  type value = D.value

  type pair = key * value

  type dict = 
    | Leaf
    | Two of dict * pair * dict
    | Three of dict * pair * dict * pair * dict

  (* INVARIANTS: 
   * 2-node: Two(left,(k1,v1),right) 
   * (1) Every key k appearing in subtree left must be k < k1.
   * (2) Every key k appearing in subtree right must be k > k1. 
   * (3) The length of the path from the 2-node to
   *     every leaf in its Two subtrees must be the same.  
   * 
   * 3-node: Three(left,(k1,v1),middle,(k2,v2),right) 
   * (1) k1 < k2.
   * (2) Every key k appearing in subtree left must be k < k1. 
   * (3) Every key k appearing in subtree right must be k > k2. 
   * (4) Every key k appearing in subtree middle must be k1 < k < k2.
   * (5) The length of the path from the 3-node to every leaf in its Three 
   *     subtrees must be the same. 
   *)

  type kicked =
    | Up of dict * pair * dict
    | Done of dict

  type hole =
    | Hole of pair option * dict
    | Absorbed of pair option * dict

  type direction2 =
    | Left2
    | Right2

  type direction3 =
    | Left3
    | Mid3
    | Right3
        
  (* How do we represent an empty dictionary with 2-3 trees? *)
  let empty : dict = Leaf

  (* 2-3 tree implementation of fold *)
  let rec fold (f: key -> value -> 'a -> 'a) (u: 'a) (d: dict) : 'a =
    match d with
      | Leaf -> u
      | Two (d1,(k,v),d2) -> fold f (f k v (fold f u d1)) d2
      | Three (d1,(k1,v1),d2,(k2,v2),d3) ->
	fold f (f k2 v2 (fold f u (Two (d1,(k1,v1),d2)))) d3

  (* insert upward phase two node *)
  let insert_upward_Two (w: pair) (w_left: dict) (w_right: dict) 
      (x: pair) (x_other: dict) : kicked = 
    let (xk,xv) = x in
    let (wk,wv) = w in
    match D.compare wk xk with
      | Less | Eq -> Done (Three (w_left,w,w_right,x,x_other))
      | Greater -> Done (Three (x_other,x,w_left,w,w_right))

  (* insert upward phase three node *)
  let insert_upward_Three (w: pair) (w_left: dict) (w_right: dict)
      (x: pair) (y: pair) (other_left: dict) (other_right: dict) : kicked =
    let (xk,xv) = x in
    let (yk,yv) = y in
    let (wk,wv) = w in
    match D.compare wk xk with
      | Less | Eq ->
	let left = Two (w_left,w,w_right) in
	let right = Two (other_left,y,other_right) in
	Up (left,x,right)
      | Greater ->
	(match D.compare wk yk with
	  | Less | Eq ->
	    let left = Two (other_left,x,w_left) in
	    let right = Two (w_right,y,other_right) in
	    Up (left,w,right)
	  | Greater ->
	    let left = Two (other_left,x,other_right) in
	    let right = Two (w_left,w,w_right) in
	    Up (left,y,right)
	)

  (* insert downward *)
  let rec insert_downward (d: dict) (k: key) (v: value) : kicked =
    match d with
      | Leaf -> Up (Leaf,(k,v),Leaf)
      | Two(left,n,right) -> insert_downward_Two (k,v) n left right
      | Three(left,n1,middle,n2,right) ->
	insert_downward_Three (k,v) n1 n2 left middle right


  (* insert downward phase on two node *)
  and insert_downward_Two ((k,v): pair) ((k1,v1): pair) 
      (left: dict) (right: dict) : kicked = 
    match D.compare k k1 with
      | Less -> 
	(match insert_downward left k v with
	  | Up (l,(ku,vu),r) -> insert_upward_Two (ku,vu) l r (k1,v1) right
	  | Done x -> Done (Two (x,(k1,v1),right))
	)
      | Eq -> Done (Two (left,(k,v),right)) 
      | Greater -> 
	(match insert_downward right k v with
	  | Up (l,(ku,vu),r) -> insert_upward_Two (ku,vu) l r (k1,v1) left
	  | Done x -> Done (Two (left,(k1,v1),x))
	)

  (* insert downward phase on three node *)
  and insert_downward_Three ((k,v): pair) ((k1,v1): pair) ((k2,v2): pair) 
      (left: dict) (middle: dict) (right: dict) : kicked =
    match (D.compare k k1, D.compare k k2) with
      | (Less,Less) ->
	(match insert_downward left k v with
	  | Up (l,(ku,vu),r) ->
	    insert_upward_Three (ku,vu) l r (k1,v1) (k2,v2) middle right
	  | Done x -> Done (Three (x,(k1,v1),middle,(k2,v2),right))
	)
      | (Greater,Less) -> 
	(match insert_downward middle k v with
	  | Up (l,(ku,vu),r) ->
	    insert_upward_Three (ku,vu) l r (k1,v1) (k2,v2) left right
	  | Done x -> Done (Three (left,(k1,v1),x,(k2,v2),right))
	)
      | (Greater,Greater) ->
	(match insert_downward right k v with
	  | Up (l,(ku,vu),r) ->
	    insert_upward_Three (ku,vu) l r (k1,v1) (k2,v2) left middle
	  | Done x -> Done (Three (left,(k1,v1),middle,(k2,v2),x))
	)
      | (_,_) -> Done (Three (left,(k,v),middle,(k2,v2),right))

  (* insert into 2-3 tree *)
  let insert (d: dict) (k: key) (v: value) : dict =
    match insert_downward d k v with
      | Up(l,(k1,v1),r) -> Two(l,(k1,v1),r)
      | Done x -> x

  (* remove upward phase on two node *)
  let remove_upward_Two (n: pair) (rem: pair option) 
      (left: dict) (right: dict) (dir: direction2) : hole =
    match dir,n,left,right with
      | Left2,x,l,Two(m,y,r) -> Hole(rem,Three(l,x,m,y,r))
      | Right2,y,Two(l,x,m),r -> Hole(rem,Three(l,x,m,y,r))
      | Left2,x,a,Three(b,y,c,z,d) ->
	Absorbed(rem,Two(Two(a,x,b),y,Two(c,z,d)))
      | Right2,z,Three(a,x,b,y,c),d ->
	Absorbed(rem,Two(Two(a,x,b),y,Two(c,z,d)))
      | Left2,_,_,_ | Right2,_,_,_ -> Absorbed(rem,Two(Leaf,n,Leaf))

  (* remove upward phase on three node *)
  let remove_upward_Three (n1: pair) (n2: pair) (rem: pair option)
      (left: dict) (middle: dict) (right: dict) (dir: direction3) : hole =
    match dir,n1,n2,left,middle,right with
      | Left3,x,z,a,Two(b,y,c),d -> Absorbed(rem,Two(Three(a,x,b,y,c),z,d))
      | Mid3,y,z,Two(a,x,b),c,d -> Absorbed(rem,Two(Three(a,x,b,y,c),z,d))
      | Mid3,x,y,a,b,Two(c,z,d) -> Absorbed(rem,Two(a,x,Three(b,y,c,z,d)))
      | Right3,x,z,a,Two(b,y,c),d -> Absorbed(rem,Two(a,x,Three(b,y,c,z,d)))
      | Left3,w,z,a,Three(b,x,c,y,d),e ->
	Absorbed(rem,Three(Two(a,w,b),x,Two(c,y,d),z,e))
      | Mid3,y,z,Three(a,w,b,x,c),d,e ->
	Absorbed(rem,Three(Two(a,w,b),x,Two(c,y,d),z,e))
      | Mid3,w,x,a,b,Three(c,y,d,z,e) ->
	Absorbed(rem,Three(a,w,Two(b,x,c),y,Two(d,z,e)))
      | Right3,w,z,a,Three(b,x,c,y,d),e ->
	Absorbed(rem,Three(a,w,Two(b,x,c),y,Two(d,z,e)))
      | Left3,_,_,_,_,_ | Mid3,_,_,_,_,_ | Right3,_,_,_,_,_ ->
        Absorbed(rem,Three(Leaf,n1,Leaf,n2,Leaf))

  (* remove downward phase *)
  let rec remove_downward (d: dict) (k: key) : hole =
    match d with
      | Leaf -> Absorbed(None,d)
      | Two(Leaf,(k1,v1),Leaf) ->
        (match D.compare k k1 with
          | Eq -> Hole(Some(k1,v1),Leaf)
          | Less | Greater -> Absorbed(None,d)
        )
      | Three(Leaf,(k1,v1),Leaf,(k2,v2),Leaf) ->
        (match D.compare k k1, D.compare k k2 with
          | Eq, _ -> Absorbed(Some(k1,v1),Two(Leaf,(k2,v2),Leaf))
          | _, Eq -> Absorbed(Some(k2,v2),Two(Leaf,(k1,v1),Leaf))
          | _, _ -> Absorbed(None,d)
        )
      | Two(l,n,r) -> remove_downward_Two k n l r
      | Three(l,n1,m,n2,r) -> remove_downward_Three k n1 n2 l m r

  (* remove downward phase on two node *)
  and remove_downward_Two (k: key) ((k1,v1): pair) 
      (left: dict) (right: dict) : hole =
    match D.compare k k1 with
      | Eq ->
        (match remove_min right with
          | Hole(None,_) -> Hole(None,left)
          | Hole(Some n,new_right) -> 
            remove_upward_Two n None left new_right Right2
          | Absorbed(None,_) -> Hole(None,left)
          | Absorbed(Some n,new_right) -> Absorbed(None,Two(left,n,new_right))
        )
      | Less -> 
        (match remove_downward left k with
          | Hole(rem,t) -> remove_upward_Two (k1,v1) rem t right Left2
          | Absorbed(rem,t) -> Absorbed(rem,Two(t,(k1,v1),right))
        )
      | Greater ->
        (match remove_downward right k with
          | Hole(rem,t) -> remove_upward_Two (k1,v1) rem left t Right2
          | Absorbed(rem,t) -> Absorbed(rem,Two(left,(k1,v1),t))
        )

  (* remove downward phase on three node *)
  and remove_downward_Three (k: key) ((k1,v1): pair) ((k2,v2): pair)
      (left: dict) (middle: dict) (right: dict) : hole =
    match D.compare k k1, D.compare k k2 with
      | Eq, _ ->
        (match remove_min middle with
          | Hole(None,_) -> Hole(None,Two(left,(k2,v2),right))
          | Hole(Some n,new_middle) -> 
            remove_upward_Three n (k2,v2) None left new_middle right Mid3
          | Absorbed(None,_) -> Absorbed(None,Two(left,(k1,v1),right))
          | Absorbed(Some n,new_middle) -> 
            Absorbed(None,Three(left,n,new_middle,(k2,v2),right))
        )
      | _ , Eq ->
        (match remove_min right with
          | Hole(None,_) -> Hole(None,Two(left,(k1,v1),middle))
          | Hole(Some n,new_right) -> 
            remove_upward_Three (k1,v1) n None left middle new_right Right3
          | Absorbed(None,_) -> Absorbed(None,Two(left,(k1,v1),middle))
          | Absorbed(Some n,new_right) -> 
            Absorbed(None,Three(left,(k1,v1),middle,n,new_right))
        )
      | Less, _ ->
        (match remove_downward left k with
          | Hole(rem,t) -> 
            remove_upward_Three (k1,v1) (k2,v2) rem t middle right Left3
          | Absorbed(rem,t) -> 
            Absorbed(rem,Three(t,(k1,v1),middle,(k2,v2),right))
        )
      | _, Greater ->
        (match remove_downward right k with
          | Hole(rem,t) -> 
            remove_upward_Three (k1,v1) (k2,v2) rem left middle t Right3
          | Absorbed(rem,t) -> 
            Absorbed(rem,Three(left,(k1,v1),middle,(k2,v2),t))
        )
      | Greater, Less ->
        (match remove_downward middle k with
          | Hole(rem,t) -> 
            remove_upward_Three (k1,v1) (k2,v2) rem left t right Mid3
          | Absorbed(rem,t) -> 
            Absorbed(rem,Three(left,(k1,v1),t,(k2,v2),right))
        )

  (* removes minimum value, helper *)
  and remove_min (d: dict) : hole =
    match d with
      | Leaf -> Hole(None,Leaf)
      | Two(Leaf,n,_) -> Hole(Some n,Leaf)
      | Three(Leaf,n1,middle,n2,right) -> Absorbed(Some n1,Two(middle,n2,right))
      | Two(left,n,right) -> 
        (match remove_min left with
          | Hole(rem,t) -> remove_upward_Two n rem t right Left2
          | Absorbed(rem,t) -> Absorbed(rem,Two(t,n,right))
        )
      | Three(left,n1,middle,n2,right) ->
        (match remove_min left with
          | Hole(rem,t) -> remove_upward_Three n1 n2 rem t middle right Left3
          | Absorbed(rem,t) -> Absorbed(rem,Three(t,n1,middle,n2,right))
        )

  (* removes a key *)
  let remove (d: dict) (k: key) : dict =
    match remove_downward d k with
      | Hole(_,d') -> d'
      | Absorbed(_,d') -> d'

  (* function that returns the value of the given key
   * in our dictionary and returns it as an option, or return None
   * if the key is not in our dictionary. *)
  let rec lookup (d: dict) (k: key) : value option =
    match d with
      | Leaf -> None
      | Two (d1,(k1,v),d2) ->
	(match D.compare k k1 with
	  | Less -> lookup d1 k
	  | Eq -> Some v
	  | Greater -> lookup d2 k
	)
      | Three (d1,(k1,v1),d2,(k2,v2),d3) ->
	(match D.compare k k1 with
	  | Less -> lookup d1 k
	  | Eq -> Some v1
	  | Greater -> 
	    (match D.compare k k2 with
	      | Less -> lookup d2 k
	      | Eq -> Some v2
	      | Greater -> lookup d3 k
	    )
	)


  let fast_lookup d k =
    match lookup d k with
      | None -> None 
      | Some v -> Some (k,v)

  (* function to test if a given key is in our dictionary *)
  let member (d: dict) (k: key) : bool =
    match lookup d k with
      | None -> false
      | Some _ -> true

  (* function that removes any (key,value) pair from our 
   * dictionary (your choice on which one to remove), and returns
   * as an option this (key,value) pair along with the new dictionary. 
   * if our dictionary is empty, this should return None. *)
  let choose (d: dict) : (key * value * dict) option =
    match d with
      | Leaf -> None
      | Two (l,(k,v),r) -> Some (k,v,remove d k)
      | Three (l,(k1,v1),m,(k2,v2),r) -> Some (k1,v1,remove d k1)

  (* determines if tree is balanced  *)
  let rec balanced (d: dict) : bool =
    match d with
      | Leaf -> true
      | Two (d1,p,d2) ->
	(match (d1,d2) with
	    | (Leaf, Two (x1,x2,x3)) -> false
	    | (Leaf, Three (x1,x2,x3,x4,x5)) -> false
	    | (Two (x1,x2,x3), Leaf) -> false
	    | (Three (x1,x2,x3,x4,x5), Leaf) -> false
	    | (_,_) -> (balanced d1) && (balanced d2)
	)
      | Three (d1,p1,d2,p2,d3) ->
	(match (d1,d2,d3) with
	  | (Leaf, Two (x1,x2,x3), _) -> false
	  | (Leaf, Three (x1,x2,x3,x4,x5), _) -> false
	  | (Leaf, _, Two (x1,x2,x3)) -> false
	  | (Leaf, _, Three (x1,x2,x3,x4,x5)) -> false
	  | (Two (x1,x2,x3), Leaf, _) -> false
	  | (Three (x1,x2,x3,x4,x5), Leaf, _) -> false
	  | (Two (x1,x2,x3), _, Leaf) -> false
	  | (Three (x1,x2,x3,x4,x5), _, Leaf) -> false
	  | (_,_,_) -> (balanced d1) && (balanced d2) && (balanced d3)
	)

  let rec length d =
    match d with
      | Leaf -> 0
      | Two (l,_,r) -> 1 + (length l) + (length r)
      | Three (l,_,m,_,r) -> 2 + (length l) + (length m) + (length r)

(*
  (********************************************************************)
  (*       tests                                                      *)
  (********************************************************************)

  (* adds a list of (key,value) pairs in left-to-right order *)
  let insert_list (d: dict) (lst: (key * value) list) : dict = 
    List.fold_left (fun r (k,v) -> insert r k v) d lst

  (* adds a list of (key,value) pairs in right-to-left order *)
  let insert_list_reversed (d: dict) (lst: (key * value) list) : dict =
    List.fold_right (fun (k,v) r -> insert r k v) lst d

  (* generates a (key,value) list with n distinct keys in increasing order *)
  let generate_pair_list (size: int) : (key * value) list =
    let rec helper (size: int) (current: key) : (key * value) list =
      if size <= 0 then []
      else 
        let new_current = D.gen_key_gt current () in
        (new_current, D.gen_value()) :: (helper (size - 1) new_current)
    in
    helper size (D.gen_key ())

  (* generates a (key,value) list with keys in random order *)
  let rec generate_random_list (size: int) : (key * value) list =
    if size <= 0 then []
    else 
      (D.gen_key_random(), D.gen_value()) :: (generate_random_list (size - 1))


  let test_balance () =
    let d1 = Leaf in
    assert(balanced d1) ;

    let d2 = Two(Leaf,D.gen_pair(),Leaf) in
    assert(balanced d2) ;

    let d3 = Three(Leaf,D.gen_pair(),Leaf,D.gen_pair(),Leaf) in
    assert(balanced d3) ;

    let d4 = Three(Two(Two(Two(Leaf,D.gen_pair(),Leaf),D.gen_pair(),
                           Two(Leaf,D.gen_pair(),Leaf)),
                       D.gen_pair(),Two(Two(Leaf,D.gen_pair(),Leaf),
                                        D.gen_pair(),
                                        Two(Leaf,D.gen_pair(),Leaf))),
                   D.gen_pair(),
                   Two(Two(Two(Leaf,D.gen_pair(),Leaf),D.gen_pair(),
                           Two(Leaf,D.gen_pair(),Leaf)),D.gen_pair(),
                       Two(Two(Leaf,D.gen_pair(),Leaf),D.gen_pair(),
                           Two(Leaf,D.gen_pair(),Leaf))),D.gen_pair(),
                   Two(Two(Two(Leaf,D.gen_pair(),Leaf),D.gen_pair(),
                           Two(Leaf,D.gen_pair(),Leaf)),D.gen_pair(),
                       Three(Two(Leaf,D.gen_pair(),Leaf),D.gen_pair(),
                             Two(Leaf,D.gen_pair(),Leaf),D.gen_pair(),
                             Three(Leaf,D.gen_pair(),Leaf,D.gen_pair(),Leaf))))
    in
    assert(balanced d4) ;

    let d5 = Two(Leaf,D.gen_pair(),Two(Leaf,D.gen_pair(),Leaf)) in
    assert(not (balanced d5)) ;

    let d6 = Three(Leaf,D.gen_pair(),
                   Two(Leaf,D.gen_pair(),Leaf),D.gen_pair(),Leaf) in
    assert(not (balanced d6)) ;

    let d7 = Three(Three(Leaf,D.gen_pair(),Leaf,D.gen_pair(),Leaf),
                   D.gen_pair(),Leaf,D.gen_pair(),Two(Leaf,D.gen_pair(),Leaf))
    in
    assert(not (balanced d7)) ;
    () 


  let test_insert () = 
    let k1 = D.gen_key () in
    let k2 = D.gen_key_gt k1 () in
    let k3 = D.gen_key_gt k2 () in
    let k4 = D.gen_key_gt k3 () in
    let v = D.gen_value () in
    let t1 = insert empty k1 v in
    let t1a = insert empty k3 v in
    let t2 = insert t1 k2 v in
    let t3 = insert t2 k3 v in
    let t4 = insert t3 k4 v in
    let t5 = insert (insert t1 k1 v) k1 v in
    assert ((balanced t1 && t1 = Two (Leaf,(k1,v),Leaf)) = true) ;
    assert ((balanced t2 && t2 = Three (Leaf,(k1,v),Leaf,(k2,v),Leaf)) = true) ;
    assert ((balanced t3 && t3 = Two (t1,(k2,v),t1a)) = true) ;
    assert ((balanced t4 && t4 = Two (t1,(k2,v), Three (
				   Leaf,(k3,v),Leaf,(k4,v),Leaf))) = true) ;
    assert ((balanced t5 && t5 = t1) = true) ;
    assert (lookup t4 k1 = Some v) ;
    assert (lookup t1 k4 = None) ;
    assert (member t4 k1 = true) ;
    assert (member t1 k4 = false) ;
    ()

  let test_choose () = 
    let k1 = D.gen_key () in
    let k2 = D.gen_key_gt k1 () in
    let k3 = D.gen_key_gt k2 () in
    let v = D.gen_value () in
    let t1 = insert empty k1 v in
    let t2 = insert t1 k2 v in
    let t3 = insert t2 k3 v in
    assert (choose empty = None) ;
    assert (choose t1 = Some(k1,v,empty)) ;
    assert (choose t2 = Some(k1,v,Two(Leaf,(k2,v),Leaf))) ;
    assert (choose t3 = Some(k2,v,Three(Leaf,(k1,v),Leaf,(k3,v),Leaf))) ;
    ()



  let test_remove_nothing () =
    let pairs1 = generate_pair_list 26 in
    let d1 = insert_list empty pairs1 in
    let r2 = remove d1 (D.gen_key_lt (D.gen_key()) ()) in
    List.iter (fun (k,v) -> assert(lookup r2 k = Some v)) pairs1 ;
    assert(balanced r2) ;
    ()

  let test_remove_from_nothing () =
    let d1 = empty in
    let r1 = remove d1 (D.gen_key()) in
    assert(r1 = empty) ;
    assert(balanced r1) ;
    ()

  let test_remove_in_order () =
    let pairs1 = generate_pair_list 26 in
    let d1 = insert_list empty pairs1 in
    List.iter 
      (fun (k,v) -> 
        let r = remove d1 k in
        let _ = List.iter 
          (fun (k2,v2) ->
            if k = k2 then assert(lookup r k2 = None)
            else assert(lookup r k2 = Some v2)
          ) pairs1 in
        assert(balanced r)
      ) pairs1 ;
    ()

  let test_remove_reverse_order () =
    let pairs1 = generate_pair_list 26 in
    let d1 = insert_list_reversed empty pairs1 in
    List.iter 
      (fun (k,v) -> 
        let r = remove d1 k in
        let _ = List.iter 
          (fun (k2,v2) ->
            if k = k2 then assert(lookup r k2 = None)
            else assert(lookup r k2 = Some v2)
          ) pairs1 in
        assert(balanced r)
      ) pairs1 ;
    ()

  let test_remove_random_order () =
    let pairs5 = generate_random_list 100 in
    let d5 = insert_list empty pairs5 in
    let r5 = List.fold_right (fun (k,_) d -> remove d k) pairs5 d5 in
    List.iter (fun (k,_) -> assert(not (member r5 k))) pairs5 ;
    assert(r5 = empty) ;
    assert(balanced r5) ;
    () 

  let run_tests () = 
    test_balance() ; 
    test_insert () ;
    test_choose () ;
    test_remove_nothing() ;
    test_remove_from_nothing() ;
    test_remove_in_order() ;
    test_remove_reverse_order() ;
    test_remove_random_order() ; 
    ()
*)
end

(******************************************************************************)

(* Argument module signature to our DICT functors *)

(* dictionary for attributes *)
module AttributeDictArg : (DICT_ARG with type key = question 
  with type value = attribute) =
struct
  type key = question
  type value = attribute
  let compare k1 k2 = int_compare k1 k2
end


(* this dictionary is for calculating entropy *)
module EntropyDictArg : (DICT_ARG with type key = attribute 
  with type value = int) =
struct
  type key = attribute
  type value = int
  let compare k1 k2 = int_compare k1 k2
end


(* An association list implementation of our DICT signature. *)
module AssocListDict(D:DICT_ARG) : (DICT with type key = D.key
  with type value = D.value) = 
struct

  type key = D.key
  type value = D.value
  type dict = (key * value) list

  (* INVARIANT: sorted by key, no duplicates *)

  let empty = [] 

  let fold f d = List.fold_left (fun a (k,v) -> f k v a) d 

  let map f d = List.map f d

  let rec lookup d k = 
    match d with 
      | [] -> None
      | (k1,v1)::d1 -> 
        (match D.compare k k1 with
          | Eq -> Some v1
          | Greater -> lookup d1 k
	  | _ -> None)

  (* easily find nth movie, good for looking up questions *)
  let rec fast_lookup (d: dict) (i: key) : (key * value) option =
    match d with
      | [] -> None
      | (k1,v1)::d1 ->
	(match D.compare i k1 with
	  | Eq -> Some (k1,v1)
	  | Greater -> fast_lookup d1 i
	  | _ -> None)

  let member d k = 
    match lookup d k with 
      | None -> false 
      | Some _ -> true

  let rec insert d k v = 
    match d with 
      | [] -> [(k,v)]
      | (k1,v1)::d1 -> 
        (match D.compare k k1 with 
          | Less -> (k,v)::d
          | Eq -> (k,v)::d1
          | Greater -> (k1,v1)::(insert d1 k v))

  let rec remove d k = 
    match d with 
      | [] -> []
      | (k1,v1)::d1 ->
	(match D.compare k k1 with 
          | Eq -> d1
          | Greater -> (k1,v1)::(remove d1 k)
          | _ -> d)
	  
  let choose d = 
    match d with 
      | [] -> None
      | (k,v)::rest -> Some(k,v,rest)

  let length d =
    List.length d
end



module EntropyDict = AssocListDict (EntropyDictArg) ;;
module AttributeDict = AssocListDict (AttributeDictArg) ;;

module type DecisionTree =
  sig

    (* decision tree type *)
    type tree

    (* terminal leaf of decision tree *)
    type t
       
    (* generate tree based on attributes of training data (several users) *)
    val generate_tree : (AttributeDict.dict * t) list -> tree
    
    (* traverse tree based on attributes supplied by user *)
    val recommend : AttributeDict.dict -> tree -> (t * t)

    (* tests functions of module *)
    val run_tests : unit -> unit
  end

(* used to calculate the most frequent of a list of ts *)
module TDictArg : (DICT_ARG with type key = genre 
  with type value = int)=
struct
  type key = genre
  type value = int
  let compare k1 k2 = int_compare k1 k2
end
module TDict = AssocListDict (TDictArg) ;;

(* Implementation of DecisionTree as a Movie Decision Tree *)
module MovieDTree : (DecisionTree with type t = genre) =
struct
  type t = genre
  type tree = Node of question * (t * t) * ((EntropyDict.key * tree) list) 
	      | Leaf of (t * t)
  
      
  (* helper functions *)  
  let unique_movies (d: AttributeDict.dict list) (q: question) 
                    : EntropyDict.dict =
    let rec unique_movies_helper (d: AttributeDict.dict list) (q: question) 
                                 (e: EntropyDict.dict) : EntropyDict.dict =
      match d with
      | [] -> e
      | hd::tl ->
	match AttributeDict.fast_lookup hd q with
	  | None -> unique_movies_helper tl q e
	  | Some (_,v) -> 
            (match (EntropyDict.lookup e v) with
              | Some c -> 
                  (unique_movies_helper tl q (EntropyDict.insert e v (c+1)))
              | None -> (unique_movies_helper tl q (EntropyDict.insert e v 1))
	    )
    in
      unique_movies_helper d q EntropyDict.empty


  (* test for unique_movies *)
  let test_unique_movies () =
    let empad = AttributeDict.empty in
    let ad1 = AttributeDict.insert empad 1 2 in
    let ad2 = AttributeDict.insert ad1 1 2 in
    let ad3 = AttributeDict.insert ad2 1 1 in
    let ad4 = AttributeDict.insert ad3 1 1 in
    let adl1 = [ad1] in
    let adl2 = ad2::adl1 in
    let adl3 = ad3::adl2 in
    let adl4 = ad4::adl3 in
    let emped = EntropyDict.empty in
    let ed1 = EntropyDict.insert emped 2 1 in
    let ed2 = EntropyDict.insert emped 2 2 in
    let ed3 = EntropyDict.insert ed2 1 1 in
    let ed4 = EntropyDict.insert ed2 1 2 in
    assert ((unique_movies adl1 1) = ed1) ;
    assert ((unique_movies adl2 1) = ed2) ;
    assert ((unique_movies adl3 1) = ed3) ;
    assert ((unique_movies adl4 1) = ed4) ;
    ()

    
  
  (* converts dictionary to list *)
  let rec dict_to_list (e: EntropyDict.dict) : EntropyDict.value list =
    if (e = EntropyDict.empty) then [] else
	(match EntropyDict.choose e with
	  | None -> raise Impossible
	  | Some (k,v,e1) -> v::(dict_to_list e1))

  let log2 x = (log x) /. (log 2.)

  (* calculates entropy for a single question *)
  let single_entropy (d: AttributeDict.dict list) (q: question) : float =
    
    let counts = unique_movies d q in
    let count_list = dict_to_list counts in
    let count_sum = List.fold_left (fun x y -> x+y) 0 count_list in
    let freqs = List.map 
      (fun x -> (float_of_int x) /. (float_of_int count_sum)) count_list in
    let freq_logs = List.map (fun x -> x *. (log2 x)) freqs in
    (List.fold_left (fun x y -> x +. y) 0. freq_logs) *. -1.

  (* finds max index of a list *)	
  let rec max_index (l: float list) (max: float) (index: int) (maxindex: int) =
    match l with
      | [] -> maxindex
      | h::t ->
	let (new_index,new_max) =
	  if h > max then (index,h) else (maxindex,max) in
       	max_index t new_max (index + 1) new_index


  let test_max_index () = 
    let list1 = [1.;2.;3.;4.;5.;6.;7.;8.;9.] in
    let list2 = [9.;8.;7.;6.;5.;4.;3.;2.;1.] in
    assert ((max_index list1 0. 0 0) = 8) ;
    assert ((max_index list2 0. 0 0) = 0) ;
    ()

  (* calculates entropy *)
  let rec entropy (d: (AttributeDict.dict * t) list) : int =
    let ad_list = List.map (fun (x,y) -> x) d in
    let rec entropies d q =
      if (q = 8) then [] else
        (single_entropy d q) :: (entropies d (q+1))
    in
    let ent_list = entropies ad_list 0 in
    max_index ent_list 0. 0 0            
  

  (* list of lists with relevant critics with same answer for q,
     also removes question *)
  let rec filter_dicts (e: EntropyDict.dict) (d: (AttributeDict.dict * t) list) 
                   (q: question)
                   : (EntropyDict.key * ((AttributeDict.dict * t) list)) list =
    match (EntropyDict.choose e) with
    | None -> []
    | Some(k,v,r) ->
      let d' = List.filter (fun (x,y) -> (AttributeDict.lookup x q = Some k)) d
        in
      (k, List.map (fun (x,y) -> (AttributeDict.remove x q , y)) d') :: 
        (filter_dicts r d q)

  (* selects which element of type t to use in the leaf *)
  let select_leaf (d: (AttributeDict.dict * t) list) : t * t =
    let ts = List.map (fun (x,y) -> y) d in
    let rec get_freqs tlist e = 
      match tlist with
	| [] -> e
	| h::t ->
	  (match (TDict.lookup e h) with
	    | Some c -> (get_freqs t (TDict.insert e h (c+1)))
	    | None -> (get_freqs t (TDict.insert e h 1))
	  )
    in
    let freqs = get_freqs ts TDict.empty in
    let (most_freq,_) = TDict.fold (fun k v u -> 
      let (k_old,v_old) = u in
      if v > v_old then (k,v) else u) (0,0) freqs
    in
    let (second,_) = TDict.fold (fun k v u ->
      let (k_old,v_old) = u in
      if (v > v_old) && (k <> most_freq) then (k,v) else u) (0,0) freqs
    in
    (most_freq,second)

  (* makes decision tree 
     (t=most recent, AttributeDict=rest) *)
  let generate_tree (d: (AttributeDict.dict * t) list) : tree =
    let rec tree_helper (d: (AttributeDict.dict * t) list) : tree =
      let ad_list = List.map (fun (x,y) -> x) d in
      let t_rec = select_leaf d in
      match (AttributeDict.choose (List.hd ad_list)) with 
      | None -> Leaf (t_rec)
      | _ ->
        let q = (entropy d) in 
        let attributes = (unique_movies ad_list q) in
        if (EntropyDict.length attributes) = 2 then Leaf (t_rec) else
          (let dict_list = (filter_dicts attributes d q) in
          Node(q,t_rec, List.map (fun (x,y) -> (x, tree_helper y)) dict_list))
    in
      tree_helper d


  
  (* looks up answer to question and finds next tree to traverse *)
  let rec list_lookup (l: (attribute * tree) list) (k: attribute) : tree option =
    match l with
      | [] -> None
      | (k1,v)::t -> if k = k1 then Some v else list_lookup t k
  
  (* uses decision tree to make genre recommendation *)
  let recommend (d: AttributeDict.dict) (x: tree) : t * t =
    let rec recommend_helper (d: AttributeDict.dict) (x: tree) : t * t =
      match x with
        | Node(q,t_rec,td) ->
	  (match AttributeDict.fast_lookup d q with
	    | Some (k,v) ->
              (match (list_lookup td k) with
		| Some b -> (recommend_helper d b)
	      	| None -> t_rec
	      )
	    | None -> t_rec
	  )
	| Leaf(t) -> t
    in
      recommend_helper d x


  let test_genrec () =
    let empad = AttributeDict.empty in
    let ad1 = AttributeDict.insert empad 1 1 in
    let ad2 = AttributeDict.insert empad 1 2 in
    let ad3 = AttributeDict.insert empad 5 8 in
    let adl1 = [(ad1,1);(ad1,1);(ad1,2)] in
    assert (recommend ad1 (generate_tree adl1) = (1,2)) ;
    assert (recommend ad2 (generate_tree adl1) = (1,2)) ;
    assert (recommend ad3 (generate_tree adl1) = (1,2)) ;
    ()

  let run_tests () =
    test_unique_movies () ;
    test_max_index () ;
    test_genrec () ;
    ()
  
end
;;

MovieDTree.run_tests () ;;
