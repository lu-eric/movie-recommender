open Hashtbl
open Decisiontree
open Hashtable

exception Improper ;;
exception ImplementMe ;;
exception Impossible ;;
exception Bad_Input of string ;;
let input_error = "\n\ninput should follow this pattern:
./project (movie: int) (rating: int 1-5) (x7 movie-rating pairs)\n\n"
;;


(* gets input from command line *)
let input = Sys.argv ;;

(* checks size of input *)
let length = Array.length input ;;

let _ = if (length < 15) then raise (Bad_Input input_error) ;;

(* removes the first element of the array, which is ./main.ml *)
let info = Array.sub input 1 (length - 1) ;;

let ints = 
  try Array.map (fun x -> int_of_string x) info
  with Failure "int_of_string" -> raise (Bad_Input "enter only ints, please!")
 ;;

(* error check input *)
let _ = Array.map (fun x -> if (x < 0) || (x > 1682) then 
    raise (Bad_Input "Movies ids are from 0 to 1682")) ints ;;

(* converts command line input to tuple *)
let into_pair x u : (int*float) list =
  match u with
    | [] -> (-1,float_of_int x)::[]
    | (-1,x1)::t -> (x,x1)::t
    | (x1,x2)::t -> (-1,float_of_int x)::u
;;

(* this is an (int * int) list, which represents (movie * rating) *)
let pairs  = Array.fold_right into_pair ints [] ;;

(* this is a convenient form for translating into the DecisionTree stuff. 
 * it replaces the movie rating with the question number *)
let nats = [1;2;3;4;5;6;7] ;;

(* replaces the movie rating with a natural number in List.map2 *)
let add_index pairs nats =
  let (movies,ratings) = List.split pairs in
  List.combine movies nats
;;

(* adds question number to movie id *)
let w_index = add_index pairs nats ;;

(* This is an AttributeDict.dict with all of the user's movies loaded into it *)
let rec to_dict d w_index =
  match w_index with
    | [] -> d
    | (x,y)::t ->
      let d' = AttributeDict.insert d x y in
      to_dict d' t
;;

(* generats input in correct format for algorithm *)
let dtree_input = to_dict AttributeDict.empty w_index ;;


(* This converts the input into a form that is useable for the
 *  Pearson correlation *)
let rec to_set s pairs =
  match pairs with
    | [] -> s
    | (x,y)::t ->
      let s' = MovieSet.insert (MovieComparable.new_m x y) s in
      to_set s' t
;;

let pearson_input = to_set MovieSet.empty pairs ;;


(******************************************************************************)

(* Parse input and create hashtables *)

(* gets user data from file line by line *)
let rec parse_users x =   
  let rec get_info pos line count = 
    if (count=3) then []
    else 
      let next = String.index_from line (pos) '\t' in 
      let x = (int_of_string(String.sub (line) (pos) (next - pos))) in 
      x::(get_info (next + 1) line (count + 1)) in 
  get_info 0 (input_line x) 0;; 

(* gets genre of movie from file, converts x|x|x|... format to int *)
let rec parse_genres x = 
  let rec get_info line = 
      let last = String.rindex line '|' in 
      let sub_start = (last - 35) in 
      let sub_string = (String.sub line sub_start 36) in
	((String.index sub_string '1')/2 + 1) in 
  get_info x;;

(* gets movie id and associated genre from data *)
let rec parse_movies x =
  let rec get_info line =   
    let first = String.index line '|' in 
    let sub_string = int_of_string(String.sub line 0 (first)) in 
    (sub_string,(parse_genres line)) in 
  get_info (input_line x);;
  
(* associates movie id int with name *)
let parse_movieNames x = 
  let get_info line =  
    let first = String.index line '|' in 
    let last = String.index line '(' in 
    let mov_string = String.sub line (first+1) (last-(first+2)) in 
    let mov_num = (String.sub line 0 first) in 
    ((mov_num),mov_string) in 
  get_info (input_line x);;

(* hashtable with movie names as keys and movie id as values *)
let rec construct_movieStringtbl2 x tbl = 
  try while true do 
      let (mov_num,mov_string) = (parse_movieNames x) in 
      Hashtbl.add tbl mov_string mov_num
    done
  with End_of_file -> ();;

(* hashtable with genre as keys and movie id as values *)
let rec construct_genreTbl x tbl = 
  try while true do 
      let (movie,genre) = (parse_movies x) in
      Hashtbl.add tbl genre movie
    done 
  with End_of_file -> ();;

(* hashtable with movie id as keys and genre as values *)
let rec construct_movieTbl x tbl =
  try while true do 
      let (movie,genre) = (parse_movies x) in 
      Hashtbl.add tbl movie genre
    done 
  with End_of_file -> ();;

(* hashtable with users as keys and moviesets as values *)
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

(* opens data files *)
let file_stream = open_in "u.data" ;;
let file_stream2 = open_in "u2.item" ;;

(* makes empty hash tables *)
let users = Hashtbl.create 1000 ;;
let movie_genre = Hashtbl.create 1000 ;;
let genre_movie = Hashtbl.create 1000 ;;
let title_int = Hashtbl.create 1000 ;;


(* populates hash tables *)
construct_userTbl file_stream users ;;
construct_movieTbl file_stream2 movie_genre ;;
construct_genreTbl file_stream2 genre_movie ;;
construct_movieStringtbl2 file_stream2 title_int ;;

(******************************************************************************)
(* runs decision tree on data *)

(* helper functions *)

let movie_to_genre k v i : AttributeDict.dict list =
  let rec movie_to_genre_helper (v: MovieSet.set) (d: AttributeDict.dict) 
                                (q: question) : AttributeDict.dict =
    match (MovieSet.choose v) with
    | None -> d
    | Some(m,rest) -> 
      let mov = MovieComparable.get_movie m in
      (movie_to_genre_helper rest 
	 (AttributeDict.insert d q (try Hashtbl.find movie_genre mov with Not_found -> 19)) (q+1))
  in
    (movie_to_genre_helper v AttributeDict.empty 1) :: i
;;

let last_movie_to_tuple (d: AttributeDict.dict)  =
  match (AttributeDict.lookup d 8) with
  | None -> raise Impossible (* at least 8 movies exist *)
  | Some(v) -> ((AttributeDict.remove d 8),v)
;;

let ls = Hashtbl.fold movie_to_genre users [] ;;
let data = List.map last_movie_to_tuple ls ;;


(* generates the decision tree based on training data *)
let dtree = MovieDTree.generate_tree data ;;

(* dtree_output is an int representing a genre. It is passed to Ethan, so he
 * can filter out movies, which are then passed to Eric *)
let dtree_output = MovieDTree.recommend dtree_input dtree ;;


(******************************************************************************)
(* Intersect this movieset with each movieset of the
   user hashtable to filter down to only relevant movies 
*)

(* gets genre of a movie *)
let find_genre x = Hashtbl.find movie_genre x ;;

(* filters relevant genres *)
let rec change_set movieTbl cur_set genreT new_set = 
  match (MovieSet.choose cur_set) with
    |None -> new_set
    |Some(element,rest) -> 
      let movie = (MovieComparable.get_movie element) in
      let (g1,g2) = genreT in
      try if ((Hashtbl.find movieTbl movie) = g1) || ((Hashtbl.find movieTbl movie) = g2) then
	 change_set movieTbl rest genreT (MovieSet.insert element new_set)
	else change_set movieTbl rest genreT new_set
      with Not_found -> change_set movieTbl rest genreT new_set
;;

(* create empty hashtable *)
let filtered_tbl = Hashtbl.create 1000 ;;

(* filter hashtable *)
let narrow_tbl1 genreT movieTbl userTbl newTbl =
  Hashtbl.iter (fun key value ->
    Hashtbl.add newTbl key (change_set movieTbl value genreT MovieSet.empty))
    userTbl ;;

(* create relevant data set for Pearson algorithm *)
let relevant_data = narrow_tbl1 dtree_output movie_genre users filtered_tbl ;;

(******************************************************************************)
(* Pearson correlation calculations *)

let final_recommendation = Hashtable.recommend pearson_input filtered_tbl 4 ;;

(* conversion function from ints to string; allows us to change function if
 * we want to print out different strings for a given movie *)
let conv_func x =
  let genre_x = string_of_int (Hashtbl.find movie_genre x) in
  let mov_int = string_of_int x in
  (mov_int) ^ "  " ^ (genre_x)
;;

let rec add_commas ints =
  match ints with
    | [] -> "\n"
    | h::[] -> (conv_func h) ^ "\n"
    | h::t -> (conv_func h) ^ "\n" ^ add_commas t
;;

let rec_string = "\n" ^ (add_commas final_recommendation) ;;

(******************************************************************************)
let main () =
  let _ = List.map (fun (x,y) -> if (y > 5.) || (y < 0.) then raise Improper) pairs in
  let _ = print_string
    "\nBased on your viewing history, we think you would like ..." in
  let _ = print_newline in
  let _ = print_string (rec_string ^ "\n") in
  let _ = flush_all () in
  ()
;;


main () ;;


