Instructions
1. First, you need to download the files. Everything should be in the zipped folders.
   Add both the code and data to the same directory.

2. You can compile the files by running “make” at the command line in the directory

3. Now run “./project” and the following command line arguments separated by spaces:
        movie1 rating1 movie2 rating2 … movie7 rating7

4. This is a total of 14 additional command line arguments.
   The movies must be ints between 1 and 1682, inclusive.
   The ratings must be ints between 0 and 5, inclusive.
   If the arguments do not meet these requirements, an exception will be thrown and an error message will inform the user.

5. The order of the input is important.
   The movies must be listed in chronological order of viewing.
   In other words movie7 is the most recent movie the user has seen.

6. Note that the user needs to look up the names of the movies against their identification numbers (ints) from the original data set.

7. After the user has entered the appropriate command line arguments, the movie recommender will take care of the rest.
   It will output five movie recommendations as movie identification numbers.
   The recommendations are based on the order of input and the ratings.