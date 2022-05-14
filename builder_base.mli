type string_builder 

val word : string -> string_builder

val concat : string_builder -> string_builder -> string_builder 

val char_at : int -> string_builder -> char 

val sub_string : int -> int -> string_builder -> string_builder

val cost : string_builder -> int

val random_string : int -> string_builder 

val list_of_string : string_builder -> string list 

val balance : string_builder -> string_builder 

val analyse : int -> int * int * float * float 

