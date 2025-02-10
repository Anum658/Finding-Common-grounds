# Requirements

  * Python 3.7
  * Jupyter Notebook
  * Installation of Sympy package (https://anaconda.org/anaconda/sympy)
  * Installation of Networkx (https://anaconda.org/anaconda/networkx)

# Execution

  * Code can be executed in the same rhythm, as it has been written. Every function is defined separately in the cell. The cells coming below are dependent on the cells defined above.

  * Coherence, Conflict, Cyclicity, and redundancy have been defined independently and can be checked by giving any sample Horn expression and background knowledge if needed.

  * Data file is given in CSV form as 'SharedResponses-mix.csv', it's been loaded in the notebook by the same name.
 
  * While creating Horn expression from the dataset after preprocessing, the user needs to define a set of countries from clusters 'east', 'west', and 'south'. Users can change it with any country name. (country name should be small letters). In Notebook, we have used

      countries_dict = {'west': ['norway'],
                                   'east': ['india'],
                                   'south': ['france']}

  * After defining countries, the user needs to update both background knowledge and the collection of symbols accordingly. Background knowledge for some countries has been defined in the notebook.
 
 * Executing the last cell, the user gives countries list as a dictionary of both background knowledge and collection of symbols, it resolves conflict and prints horn expression, and then it outputs a common ground after resolving incoherence if exists.
