exception ImplementMe
type order = Less | Eq | Greater ;;



(* An interface for set modules *)
module type SET = 
sig
  type elt  (* type of elements in the set *)
  type set  (* abstract type for the set *)

  val empty : set

  val is_empty : set -> bool

  val insert : elt -> set -> set

  (* same as insert x empty *)
  val singleton : elt -> set

  val union : set -> set -> set
  val intersect : set -> set -> set

  (* remove an element from the set -- if the
   * element isn't present, does nothing. *)
  val remove : elt -> set -> set

  (* returns true iff the element is in the set *)
  val member : set -> elt -> bool

  (* chooses some member from the set, removes it 
   * and returns that element plus the new set.  
   * If the set is empty, returns None. *)
  val choose : set -> (elt * set) option

  (* fold a function across the elements of the set
   * in some unspecified order. *)
  val fold : (elt -> 'a -> 'a) -> 'a -> set -> 'a

  (* returns the number of elements in the set *)
  val length : set -> int

  (* prints out the elements in the set *)
  val print: set -> unit
end


(* parameter to Set modules -- we must pass in some 
 * type for the elements of a set, a comparison
 * function, and a way to stringify it.
 *)
module type COMPARABLE = 
sig
  type t
  val compare : t -> t -> order
  val new_m: int -> float -> t
  val elt_to_string : t -> string
  val get_rating : t -> float
  val get_movie : t -> int

end


(* An example implementation of our COMPARABLE signature. Use this
 * struct for testing. *)
module MovieComparable : COMPARABLE =
struct
  type t = int * float
  let new_m x y = (x, y)
  let compare x y = 
    let (a, b) = x in 
    let (c, d) = y in 
    if a < c then Less else if a > c then Greater else Eq
  let elt_to_string x =
    let (a, b) = x in 
    "Movie: " ^ string_of_int a ^ "\nValue:" ^ string_of_float b
  let get_rating x = 
    let (a, b) = x in
    b
  let get_movie x = 
    let (a, b) = x in
    a 
end


module ListSet(C: COMPARABLE) : (SET with type elt = C.t) = 
struct
  type elt = C.t 
  type set = elt list

  (* INVARIANT: sorted, no duplicates *)
  let empty = []
  let is_empty xs = 
    match xs with 
      | [] -> true
      | _ -> false
  let singleton x = [x]
  let rec insert x xs = 
    match xs with 
      | [] -> [x]
      | y::ys -> (match C.compare x y with 
          | Greater -> y::(insert x ys)
          | Eq -> xs
          | Less -> x::xs)

  let union xs ys = List.fold_right insert xs ys
  let rec remove y xs = 
    match xs with 
      | [] -> []
      | x::xs1 -> (match C.compare y x with 
          | Eq -> xs1
          | Less -> xs
          | Greater -> x::(remove y xs1))

  let rec intersect xs ys = 
    match xs, ys with 
      | [], _ -> []
      | _, [] -> []
      | xh::xt, yh::yt -> (match C.compare xh yh with 
          | Eq -> xh::(intersect xt yt)
          | Less -> intersect xt ys
          | Greater -> intersect xs yt)

  let rec member xs x = 
    match xs with 
      | [] -> false
      | y::ys -> (match C.compare x y with
          | Eq -> true
          | Greater -> member ys x
          | Less -> false)

  let choose xs = 
    match xs with 
      | [] -> None
      | x::rest -> Some (x,rest)

  let fold f e = List.fold_left (fun a x -> f x a) e 
    
  let rec length xs = 
    List.length xs

  let rec print xs = 
    match xs with 
      | [] -> print_endline "Empty"
      | hd::tl -> print_endline (C.elt_to_string hd); print tl
end


module MovieSet = ListSet(MovieComparable)

(*****************************************************************************)
(* functions from file io *)
let rec parse_users x =   
  let rec get_info pos line count = 
    if (count=3) then []
    else 
      let next = String.index_from line (pos) '\t' in 
      let x = (int_of_string(String.sub (line) (pos) (next - pos))) in 
      x::(get_info (next + 1) line (count + 1)) in 
  get_info 0 (input_line x) 0;; 

let rec parse_genres x = 
  let rec get_info line = 
      let last = String.rindex line '|' in 
      let sub_start = (last - 35) in 
      let sub_string = (String.sub line sub_start 36) in
      ((String.index sub_string '1')/2) in 
  get_info x;;

let rec parse_movies x =
  let rec get_info line =   
    let first = String.index line '|' in 
    let sub_string = int_of_string(String.sub line 0 (first)) in 
    (sub_string,(parse_genres line)) in 
  get_info (input_line x);;
  

let rec construct_genreTbl x tbl = 
  try while true do 
      let (movie,genre) = (parse_movies x) in
      Hashtbl.add tbl genre movie
    done 
  with End_of_file -> ();;

let rec construct_movieTbl x tbl =
  try while true do 
      let (movie,genre) = (parse_movies x) in 
      Hashtbl.add tbl movie genre
    done 
  with End_of_file -> ();;

let rec construct_userTbl x tbl = 
  try while true do 
      match parse_users x with
	| [] -> failwith "Not Possible"
	| _::[] -> failwith "Not Possible"
	| _::_::[] -> failwith "Not Possible"
	| user::movie::rating::_ ->
	  if Hashtbl.mem tbl user then 
	    let firstset = Hashtbl.find tbl user in
	    Hashtbl.replace tbl user 
	      (MovieSet.insert (MovieComparable.new_m movie 
				  (float_of_int rating)) firstset)
	  else Hashtbl.add tbl user 
	    (MovieSet.insert (MovieComparable.new_m movie 
				(float_of_int rating)) MovieSet.empty)
    done 
  with End_of_file -> ();;

(*****************************************************************************)

(*
 * The recommend function takes in the user's MovieSet, 
 * a master hashtable that contains critics and their MovieSets, 
 * and finally a number of recommendations that we want to generate.
 * 
 * This function will ultimately output a list of ints, 
 * representing movies, that can be recommended for the user to watch
 *) 


let recommend (master_userset: MovieSet.set) 
    (master_tbl: (int, MovieSet.set) Hashtbl.t) 
    (master_number: int) =

  let score (a: MovieSet.set) (b: MovieSet.set) : float = 
    
  (* first return the intersection of the two MovieSets *)
    let rec mutual (c: MovieSet.set) 
	(d: MovieSet.set) (temp: MovieSet.set) : MovieSet.set = 
      match MovieSet.choose c with
	| None -> temp
	| Some (elt, set) -> 
	  if MovieSet.member d elt 
	  then mutual set d (MovieSet.insert elt temp)
	  else mutual set d temp in
    let new_a = mutual a b MovieSet.empty in
    let new_b = mutual b a MovieSet.empty in

    let test1 = MovieSet.insert (MovieComparable.new_m 1 1.) MovieSet.empty in
    let test1 = MovieSet.insert (MovieComparable.new_m 2 2.) test1 in 
    let test1 = MovieSet.insert (MovieComparable.new_m 3 3.) test1 in
    let test1 = MovieSet.insert (MovieComparable.new_m 4 4.) test1 in
    let test1 = MovieSet.insert (MovieComparable.new_m 5 5.) test1 in
    
    let test2 = MovieSet.insert (MovieComparable.new_m 2 5.) MovieSet.empty in
    let test2 = MovieSet.insert (MovieComparable.new_m 3 5.) test2 in
    let test2 = MovieSet.insert (MovieComparable.new_m 4 5.) test2 in
    let test2 = MovieSet.insert (MovieComparable.new_m 5 5.) test2 in
    let test2 = MovieSet.insert (MovieComparable.new_m 6 1.) test2 in

    let test3 = mutual test1 test2 MovieSet.empty in

    let _ = assert (MovieSet.length test3 = 4) in

  (* add returns the sum of all the elements in a set *)
    let rec add (e: MovieSet.set) (sum: float) : float = 
      match MovieSet.choose e with
	| None -> sum
	| Some (elt, set) -> 
	  add set ((MovieComparable.get_rating elt) +. sum) in
    
    let _ = assert (add test1 0. = 15.) in
    let _ = assert (add test2 0. = 21.) in

  (* returns the sum of squares of all the elemetns in a set *)
    let rec add_squares (g: MovieSet.set) (sum: float) : float = 
      match MovieSet.choose g with
	| None -> sum
	| Some (elt, set) ->
	  add_squares set 
	    ((MovieComparable.get_rating elt) *. 
		(MovieComparable.get_rating elt) +. sum) in
    
    let _ =  assert (add_squares test1 0. = 55.) in
    let _ = assert (add_squares test2 0. = 101.) in

  (* returns a float of the products of all the elements in both sets *)
    let rec add_products (h: MovieSet.set) 
	(i: MovieSet.set) (sum: float) : float =
      match MovieSet.choose h with
	| None -> sum
	| Some (elt1, set1) ->
	  match MovieSet.choose i with
	    | None -> sum
	    | Some (elt2, set2) -> 
	      add_products set1 set2
		((MovieComparable.get_rating elt1) *. 
		    (MovieComparable.get_rating elt2) +. sum) in
    
    let _ = assert (add_products test1 test2 0. = 55.) in

  (* our implementation of the Pearson's algorithm *)
    let pearsons1 (sum1: float) (sum2: float) (sum1Sq: float) 
	(sum2Sq: float) (pSum: float) (n: int) : float = 
      let num = pSum -. (sum1 *. (sum2 /. (float_of_int n))) in
      let den = sqrt ((sum1Sq -. ((sum1 *. sum1) /. (float_of_int n)))
		      *. (sum2Sq -. ((sum2 *. sum2) /. (float_of_int n)))) in
      if den = 0. then 0. else num /. den in
    pearsons1 (add new_a 0.) (add new_b 0.) (add_squares new_a 0.) 
      (add_squares new_b 0.) (add_products new_a new_b 0.) (MovieSet.length new_a) in
  
  
(* takes in a user's MovieSet and assigns a correlation to every element *)
  let pearsons (userset: MovieSet.set) (tbl: (int, MovieSet.set) Hashtbl.t) : (int, float) Hashtbl.t =
    let newT = Hashtbl.create (Hashtbl.length tbl) in
    let f x y = Hashtbl.add newT x (score userset y) in
    Hashtbl.iter f tbl;
    newT in
  let temporary_pearsons = pearsons master_userset master_tbl in
  
(* returns the highest correlated user in a Hashtable *)
  let greatest (tbl: (int, float) Hashtbl.t) : int * float = 
    let f k v record = 
      let (key, value) = record in 
      if v > value then (k, v) else (key, value) in
    Hashtbl.fold f tbl (0, -2.) in
  
(* returns the highest n correlated users in a hashtable *)
  let rec greatest_n (tbl: (int, float) Hashtbl.t) (n: int) 
      (lst: int list) : int list = 
    if n <= 0 then List.rev lst else (
      let (a, b) = greatest tbl in
      let _ = Hashtbl.remove tbl a in
      greatest_n tbl (n-1) (a::lst)) in

  let top_users = greatest_n temporary_pearsons master_number [] in

(* returns the list of corresponding moviesets 
   to the highest correlated users *)
  let rec criticset (lst: int list) 
      (tbl: (int, MovieSet.set) Hashtbl.t) : MovieSet.set list =
      match lst with 
	| [] -> []
	| hd::tl -> (Hashtbl.find tbl hd)::(criticset tl tbl) in

  let set_list = criticset top_users master_tbl in

(* takes two MovieSets a and b and returns all values in b that 
   are not in a. This is used to make recommendations *)
  let rec not_watched (userset: MovieSet.set) (criticset: MovieSet.set)
      (temp: MovieSet.set) = 
    match MovieSet.choose criticset with
      | None -> temp
      | Some (elt, rest) ->
	if MovieSet.member userset elt 
	then not_watched userset rest temp
	else not_watched userset rest (MovieSet.insert elt temp) in

(* makes a movie list from a movie set *)
  let rec make_list (set: MovieSet.set) : int list = 
    match MovieSet.choose set with
      | None -> []
      | Some (elt, rest) -> let movie = MovieComparable.get_movie elt in
			    movie::(make_list rest) in

(* creates a movie recommendation list from a list of Moviesets. *)
  let rec setlist_to_movielist (setlist: MovieSet.set list) (current: int list) : int list = 
    match setlist with 
      | [] -> current
      | hd::tl -> let newmovies = not_watched master_userset hd MovieSet.empty in 
		  let movielist = make_list newmovies in 
		  setlist_to_movielist tl movielist@current in
  

  let duplicatelist = setlist_to_movielist set_list [] in

(* take a list and return the mode.
   sort the list, run-time encode, then sort again, then return the highest values *)
  let rec to_run_length (lst:int list) : (int * int) list =
    match lst with
      | hd::tl -> (match (to_run_length tl) with
	  | (i,c)::tl -> if hd = c then (i+1,c)::tl
	    else (1,hd)::(i,c)::tl
	  | [] -> [1,hd]
      )
      | [] -> [] in

  let sort_run_length (first: int * int) (second: int * int) : int = 
    let (a, b) = first in 
    let (c, d) = second in
    if a > c then (-1) else if a = c then 0 else (1) in

  let rec top_n_recs (recommendations: int list) (n: int) : (int * int) list = 
    let sorted = List.sort compare recommendations in
    let encoded = to_run_length sorted in 
    let final_sorted = List.sort sort_run_length encoded in
    match final_sorted with
      | [] -> []
      | hd::tl -> let rec find_n (l: (int * int) list) (m: int) : (int * int) list = 
		    if m <= 0 then [] else
		      match l with 
			| [] -> []
			| h::t -> h::(find_n t (m-1)) in
		  hd::(find_n tl n) in

  let sorted = top_n_recs duplicatelist master_number in

  let rec make_final_recommendations (lst: (int * int) list) : int list = 
    match lst with
      | [] -> []
      | hd::tl -> let (a, b) = hd in 
		  b::(make_final_recommendations tl) in

make_final_recommendations sorted;;


