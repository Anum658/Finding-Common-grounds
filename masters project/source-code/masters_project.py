#!/usr/bin/env python
# coding: utf-8

# In[2]:


from sympy import *
import networkx as nx
from sympy.logic.boolalg import Not, And, Or
from sympy.logic.inference import satisfiable
from sympy.logic.inference import entails
from itertools import *
from itertools import combinations
import itertools as it
import itertools    
import copy
import pandas as pd
from IPython.display import display
import pycountry
from collections import defaultdict
import time


# # Coherence of Horn Expression

# ## 1.  Entailment 

# In[3]:


def check_Hornexpr_entailment(F):
    
    count = 0
    #checck for all the clauses in F
    for clause in F:
        #expression without that clause
        F_without_clause = [x for x in F if x is not clause]
        if not entails(clause, F_without_clause):
            count +=1
    
    #if entailment condition is true for all clauses, it satisfies first condition
    if count == len(F):
        return True
    else:
        return False 


# ## 2. Derivations

# #### Extract Antecedents and consequents of Clauses

# In[4]:


#define a function, that takes input as clause, and extract antacedent and consequent
def extract_ant_con(clause):
    
    if type(clause.args[0]) == And:
        antacedent = set(clause.args[0].args)
    else:
        antacedent = {clause.args[0]}
        
    consequent = clause.args[1].atoms()
        
    return antacedent, consequent


# ### Excludents

# In[5]:


#define a function to extract symbols from the clause
def extract_symbols(F):
    atoms= []
    for clause in F:
        atoms.append(list(clause.args[0].atoms()))
        
    flat_list = [item for sublist in atoms for item in sublist]
    symbol_list = list(set(flat_list))
    
    return symbol_list


# #### Function to get excludents of symbols using background knowledge

# In[6]:


#define a function to get excludents using background knowledge 
def get_excludents(background_know, atom):

    excludent_atoms = []
    
    #extract symbols from backgroun knowledge
    symbol_background_know = extract_symbols(background_know)

    #check for all the symbols from backgroun knowledge
    for symbol in symbol_background_know:
        clause = Implies((symbol & atom), False)
        
        if clause in background_know:
            excludent_atoms.append(symbol)
            
    return excludent_atoms


# #### Check if two clauses have derivation w.r.t. each other while checking excludents condition

# In[7]:


#function takes input as expression, and two clauses, return true if derivation exists
def clauses_derivation(clause1, clause2, F):
    
    count = 0
    ant_clause1 = extract_ant_con(clause1)[0]
    ant_clause2 = extract_ant_con(clause2)[0]
    
    #copy the expression to extend it
    copy_expr = copy.deepcopy(F)
    copy_expr.extend(ant_clause1)

    #check entailment for all the antacedents
    for atom in ant_clause2:
        if entails(atom, copy_expr):
            count +=1
            
    if count == len(ant_clause2):
        return True
    else:
        return False


# In[8]:


#define a function to generate all possible combinations of horn expressions
def generate_combinations(F):
    
    # generate combinations of size 2
    combinations = list(itertools.combinations(F, 2))
    
    for comb in combinations:
        #removing comination that have same clauses
        if comb[0] == comb[1]:
            combinations.remove(comb)
            
    return combinations


# #### Check derivation condition for whole Horn Expression

# In[9]:


def check_Hornexpression_derivation(F):
    
    count = 0
    #generate combinations using funtion
    combinations = generate_combinations(F)
    
    #check for all combinations
    for comb in combinations:
        if not clauses_derivation(comb[0], comb[1], F) and not clauses_derivation(comb[1], comb[0], F) or comb[0] == comb[1] :
            count += 1
            
    #if derivation condition is true for all the combinations 
    if count == len(combinations):
        return True
    else:
        return False


# ## Coherence

# #### Check coherence of random clause w.r.t. Horn Expression

# In[10]:


def check_clause_coherence(F, random_clause):
    
    count1 = 0
    count2 = 0
    
    F_without_clause = [x for x in F if x != random_clause]
    con_random_clause = next(iter(extract_ant_con(random_clause)[1]))
    
    if not entails(random_clause, F_without_clause):
        
        #if all clauses in expression are coherent with the random clause
        for clause in F:
            con_clause = next(iter(extract_ant_con(clause)[1]))
            
            if con_clause not in get_excludents(background_know, con_random_clause):               
                count1 += 1
            
                if not clauses_derivation(random_clause, clause, F):
                    count2 +=1  
                
    if count1 == count2:
        return True
    else:
        return False


# #### Check Horn Expression Coherence

# In[11]:


def hornExpression_coherence(F, background_know):
    
    #combine all the functions to check coherence of Horn expression
    if check_Hornexpr_entailment(F) and check_Hornexpression_derivation(F):
        return True
    else:
        return False


# # Check cyclic Behavior of Horn Expression

# Function checks for cycles in horn expression and returns:
# 1. Same Horn expreesion if there is no cycle.
# 2. If there is a cycle, it removes cycle and returns Horn expression after removing cycles.

# In[12]:


def check_cycle(F):
    
    #fig, ax = plt.subplots(figsize=(6, 6))
    G = nx.DiGraph()
    for clause in F:
        #draw nodes as premises and consequences of implications
        G.add_node(clause.args[1])
        G.add_node(clause.args[0])
        G.add_edge(clause.args[0],clause.args[1])
    
    #draw graphs to check cycles
    options = {"edgecolors": "tab:gray", "node_size": 2550, "alpha": 0.9,"font_size": 13}
    pos = nx.shell_layout(G)
    nx.draw(G, pos, **options, with_labels = True, node_color="tab:pink",arrowsize=20, edge_color = 'green')
    plt.axis("off")
    plt.show()
    
    #detect cycle in graph
    if nx.is_directed_acyclic_graph(G):
        print('\n-----------------------------This expression has no cycles-----------------------------\n')
        return F
    
    #remove the cycle clause
    else:
        #check for cycles until no cycle is left
        while not nx.is_directed_acyclic_graph(G):
            cycle = nx.find_cycle(G, orientation="original")
            print('This expression has cycle: ', cycle)
            
            #last edge of the cycle
            tuple_clause = cycle[-1][:-1]
            print(tuple_clause)
            clause_to_remove = Implies(tuple_clause[0], tuple_clause[1])
            
            #remove last edge(clause) to remove cycle
            expr_without_cycle = [x for x in F if x != clause_to_remove]

        print('\n-------------------------------------------------------')
        print('\n Horn Expression after removing cycle is: ')
        return expr_without_cycle


# # Check Redundancy of Horn Expression

# This function checks redundancy of a Horn expression.

# In[13]:


def non_redundant_expr(F):
    
    count = 0
    for clause in F: 
        
        #hornexpression without that clause
        expr_without_clause = [x for x in F if x != clause]
        
        if not entails(clause, expr_without_clause):
            count +=1
    
    if count == len(F):
        return True
    else:
        return False


# This function runs until a expression becomes non-redundant after removing redundant clauses from the horn expression, one clause for each iteration of while loop.

# In[14]:


def check_redundancy(F):
         
    if non_redundant_expr(F):
        print('\n-------------------------This Horn Expression already is Non-Redundant-------------------------\n')
        return F
    else:
    #check for all the clauses
        for clause in F: 

            #hornexpression without that clause
            expr_without_clause = [x for x in F if x != clause]

            if entails(clause, expr_without_clause):

                #update F as without the clause
                F = expr_without_clause

                #check non redundancy of updated expression
                while non_redundant_expr(F):
                    
                    print('\n-------------------------This Horn Expression is Non-Redundant now-------------------------\n')

                    return F


# # Conflict In Horn Expression

# #### Check conflict between two specific clauses

# In[15]:


#function takes clauses as input and check conflict in between them
def check_conflict_clauses(F, clause1, clause2, background_know):
    
    ant_clause1 = extract_ant_con(clause1)[0]
    ant_clause2 = extract_ant_con(clause2)[0]
    
    #remove ant of clause 1 from ant of clause 2
    ant_diff = [x for x in ant_clause1 if x not in ant_clause2]
    if len(ant_diff) != 0:
        for atom in ant_diff:
            excludent_atom = get_excludents(background_know, atom)
            
            for i in excludent_atom:
                add_ant_to_clause = Implies((clause2.args[0] & i), clause2.args[1])
                F_without_clause = [x for x in F if x != clause2]
                
                if check_clause_coherence(F_without_clause, add_ant_to_clause):
                    return False
    else:
        return True


# #### Check Horn expression conflict by checking conflict between each possile combination of clauses

# In[16]:


def check_conflict_expr(F, background_know):
    
    count = 0
    combinations_expr = generate_combinations(F)
    
    for clause in combinations_expr:
        
        con_clause1 = next(iter(extract_ant_con(clause[0])[1]))
        con_clause2 = next(iter(extract_ant_con(clause[1])[1]))
        
        #check conflict between every to clauses
        if check_conflict_clauses(F, clause[0], clause[1], background_know) and clauses_derivation(clause[0], clause[1], F) and con_clause1 in get_excludents(background_know, con_clause2):
            count +=1
            
    if count > 0:
        return True
    else:
        return False


# # Resolve Conflict

# We can resolve conflict by:
# 1. Check conflict between each possible combination of clauses of horn expression.
# 2. If it is found, resolve by most general symbol using collection of symbols associated with each clause, and background knowledge 2.

# In[17]:


def resolve_conflict(F, background_know, col_symbols, background_know_2):
    
    #copy expression to update it
    copy_expr = copy.deepcopy(F)
    
    while check_conflict_expr(copy_expr, background_know):

        #clauses = generate_combinations(F)
        dict_of_clauses = {i : copy_expr[i] for i in range(0, len(copy_expr))}

        for i in generate_combinations(dict_of_clauses):

            clause1 = dict_of_clauses[i[0]]
            clause2 = dict_of_clauses[i[1]]
            
            #extract concludents of clauses
            con_clause1 = next(iter(extract_ant_con(clause1)[1]))
            con_clause2 = next(iter(extract_ant_con(clause2)[1]))
            

            #check conflict between two clauses
            if check_conflict_clauses(copy_expr, clause1, clause2, background_know) and clauses_derivation(clause1, clause2, copy_expr) and con_clause1 in get_excludents(background_know, con_clause2):
                print(clause1, clause2)
                for region in background_know_2:
                    
                    #for first iteration it would replace by most general symbol
                    if clause2 in F:
                        if col_symbols[i[1]] in region.args:
                            update_ant = clause2.replace(clause2.args[0], And(clause2.args[0], region.args[1]))

                        #and update the expression
                            copy_expr[i[1]] = update_ant
                    
                    #for the next iteration if conflict exists, it would replace general by specific one
                    else:
                        if clause1.args[0].atoms().intersection(region.args[1].atoms()) == clause2.args[0].atoms().intersection(region.args[1].atoms()):
                            clause1 = clause1.subs(region.args[1], col_symbols[i[0]])
                            clause2 = clause2.subs(region.args[1], col_symbols[i[1]])

                        copy_expr[i[0]] = clause1
                        copy_expr[i[1]] = clause2

    #return non repititve expression
    return [*set(copy_expr)]


# # Resolve Incoherence

# ## Safe pairse of clauses

# We search for safe pair using dependancy graphs, in case of incoherence, that we can modify to change expression into Coherent one.

# In[18]:


def get_safe_pairs(F):
    
    #fig, ax = plt.subplots(figsize=(5, 5))
    G = nx.DiGraph()
    clauses = list(itertools.combinations(F, 2))
    inverted_clauses = [t[::-1] for t in clauses]

    indices = list((i+1,j+1) for ((i,_),(j,_)) in itertools.combinations(enumerate(F), 2))
    selected_clauses = []
    options = {"edgecolors": "tab:gray", "node_size": 2550, "alpha": 0.9,"font_size": 13, }
    
    for i in range(len(clauses)):
        #first we add vertices of dependancy graph
        if clauses[i][0].args[1] in get_excludents(background_know, clauses[i][1].args[1]) and (clauses_derivation(clauses[i][0],clauses[i][1],F) or clauses_derivation(clauses[i][1],clauses[i][0],F)):
            selected_clauses.append(clauses[i])
            G.add_node((indices[i][1], indices[i][0]))
    
    #invert clasues to update second clause of pair 
    inverted_clauses = [t[::-1] for t in selected_clauses]
    s_clauses = generate_combinations(inverted_clauses)
    
    for clause in s_clauses:
        if next(iter(extract_ant_con(clause[0][1])[1])) in extract_ant_con(clause[1][1])[0] and bool(extract_ant_con(clause[0][0])[0] & extract_ant_con(clause[1][0])[0]):
            G.add_edge((F.index(clause[0][0])+1,F.index(clause[0][1])+1),(F.index(clause[1][0])+1,F.index(clause[1][1])+1))
            
        elif next(iter(extract_ant_con(clause[1][1])[1])) in  extract_ant_con(clause[0][1])[0] and bool(extract_ant_con(clause[0][0])[0] & extract_ant_con(clause[1][0])[0]):
            G.add_edge((F.index(clause[1][0])+1,F.index(clause[1][1])+1), (F.index(clause[0][0])+1,F.index(clause[0][1])+1))
            
    #pos = nx.shell_layout(G)
    #nx.draw(G, pos, with_labels = True, **options, node_color="tab:pink",arrowsize=20, edge_color = 'green')
    #plt.axis("off")
    #plt.show()
    non_safe_pairs = []
    safe_pairs = [] 
    for node in G:
        if not list(G.predecessors(node)):
            safe_pairs.append((F[node[0]-1], F[node[1]-1]))
            #print('Safe pair is: ',node)
        else:
            non_safe_pairs.append(node)
            
    if len(non_safe_pairs) == G.number_of_nodes():
        print('There is no safe pairs')
        return False
    else:
        return safe_pairs


# ### Get weaker Version of Clause

# We get weaker Version of Clauses that we can use for safe pairse to make expression coherent

# In[19]:


def weaker_version_clause(F, clause1, clause2):
    
    ant_clause1 = extract_ant_con(clause1)[0]
    ant_clause2 = extract_ant_con(clause2)[0]
    
    ant_diff = [x for x in ant_clause1 if x not in ant_clause2]
    #if there is no difference in antacedents, we call for recursion
    if len(ant_diff) == 0:
        return weaker_version_clause(F, clause2, clause1)
    else:
        excludent_atom = get_excludents(background_know, ant_diff[0])
        for i in excludent_atom:
            weaker_clause = Implies(clause2.args[0] & i, clause2.args[1])
            F_without_clause = [x for x in F if x != clause2]
            
            #if weaker clause is coherent with horn expression without clause, we return indices if same clauses is occuring
            # in more than one indices
            if check_clause_coherence(F_without_clause, weaker_clause):
                indices = [i for i, x in enumerate(F) if x == clause2]
                return weaker_clause, indices
            else:
                return False


# # Building Coherent Horn Expression Algorithm 

# In[20]:


def find_common_ground(F, background_know, background_know_2, col_symbols):
    
    #check if F is acyclic, it returns acyclic F, even if it has cycles
    F = check_cycle(F)   
    
    #check if F is non redundnant, it returns non redundant F  
    F =  check_redundancy(F)
    
    #check if F has conflict
    if not check_conflict_expr(F, background_know):
        
        print('\n----------------------------- F is not in conflict -----------------------------\n')
    
    #if it has, resolve conflict
    else:
        F = resolve_conflict(F, background_know, col_symbols, background_know_2)
        
        print('\n----------------------------- Conflict is resolved -----------------------------\n', F)
    
    #check if expression is coherent and run a while loop, until expression becomes coherent
    while not hornExpression_coherence(F, background_know):
        
        print('\n----------------------------- Resolving Incoherence -----------------------------\n')

        #extract safe pair from F
        safe_pairs =  get_safe_pairs(F)
        for safe_pair in safe_pairs:
            
            #divide safe clause into two clauses
            clause1 = safe_pair[0]
            clause2 = safe_pair[1]

            #generate weaker version of clauses
            weaker_version, indices = weaker_version_clause(F, clause1, clause2)
            
            #track the indices and update the clause
            F = [weaker_version if F.index(x) in indices else x for x in F]

    print('\n----------------------------- Expression is coherent now -----------------------------\n')
    return F


# # Moral Machine Experiment Dataset

# ### Load dataset

# In[21]:


#load dataset from csv file
df = pd.read_csv(r"SharedResponses-mix.csv")
pd.set_option('display.max_columns', None)
#pd.set_option('display.max_rows', None)


# ### Preprocessing of Dataset

# Dropping Random and none values from the dataset

# In[22]:


df = df[df.ScenarioType != 'Random']
df = df.dropna(subset = ['UserCountry3'])
df = df.dropna(subset = ['ScenarioType'])


# #### Change country names 3 letters code to full name

# In[23]:


full_name = []
for code in df['UserCountry3']:
    full_name.append(pycountry.countries.get(alpha_3=code).name.lower().replace(" ", ""))
df.loc[:,'UserCountry3'] = full_name

#data columns to lower case
df['AttributeLevel'] = df['AttributeLevel'].str.lower()
df['ScenarioType'] = df['ScenarioType'].str.lower()
df['AttributeLevel'] = df['AttributeLevel'].str.replace('hoomans','humans')
df.replace("social status", "socialstatus", inplace=True)


# ### Filter dataset according to frequency of scenerios for each country

# In[ ]:


def get_filtered_data(df, countries_list):
    
    #Filter dataset based on list of countries
    dataset = df[(df.UserCountry3.isin(countries_list))]
    
    #filtering data for pedistrains only, green and red signals only
    dataset = dataset[dataset.PedPed == 1]
    dataset = dataset[(dataset.CrossingSignal == 1) | (dataset.CrossingSignal == 2)]
    
    #group data based on same column value
    dataset = dataset.groupby(['CrossingSignal','ScenarioType','AttributeLevel','UserCountry3','Saved']).size().reset_index(name='Count')
    dataset = dataset[dataset.duplicated(subset=['ScenarioType','AttributeLevel'], keep=False)]
    
    #we only keep the rules with highest frequency occuring in dataset
    dataset = dataset.sort_values('Count', ascending=False).drop_duplicates(['CrossingSignal','ScenarioType','AttributeLevel','UserCountry3']).sort_index()

    return dataset


# ### Get clauses from the dataset

# In[ ]:


def get_clauses(data):
    
    clauses = []
    symbols_col = []
    
    for index, row in data.iterrows():
        if row["CrossingSignal"] == 1:
            row["CrossingSignal"] = symbols('green')
        else:
            row["CrossingSignal"] = symbols('red')
        row["ScenarioType"] = symbols(row["ScenarioType"])
        row["AttributeLevel"] = symbols(row["AttributeLevel"])
        row["UserCountry3"] = symbols(row["UserCountry3"])   
        if row["Saved"] == 1:
            row["Saved"] = symbols('saved')
        else:
            row["Saved"] = symbols('not_saved')
        clauses.append(Implies((row["CrossingSignal"] & row["ScenarioType"] & row["AttributeLevel"]), (row["Saved"])))
        
        #countriy name is associated with each clause
        symbols_col.append(row["UserCountry3"])
        
    return clauses, symbols_col


# ### Get Horn expression and symbols collection from Dataset

# In[ ]:


#define countries as part of regions

countries_dict = {'west': ['norway'],
                 'east': ['india'],
                 'south': ['france']}


countries_list = [item for sublist in list(countries_dict.values()) for item in sublist]


#we define backgound knowledege 2 as definite clauses, where country name implies region, so specfic symbol to general one
background_know_2 = []
for key in countries_dict:
    for value in countries_dict[key]:
        background_know_2.append(Implies(symbols(value), symbols(key)))
                  

#getting horn expression and collection of symbols using dataset and countries names list
horn_expression, collection_of_symbols =  get_clauses(get_filtered_data(df, countries_list))


# ### Declaring Symbols and defining background knowledge for each symbol

# In[ ]:


#declare all symbols
india, not_india, norway, not_norway, france, not_france, east, west, south, not_east, not_west, not_south,saved, not_saved, fit, female, old, more, low, humans, less, male, pets, fat, young, high, green, red, fitness,gender, age, utilitarian, socialstatus, species 
= symbols('india, not_india, norway, not_norway, france, not_france, east, west, south,not_east, not_west, not_south, saved, not_saved, fit, female, old, more, low, humans, less, male, pets,fat, young, high, green, red, fitness, gender, age, utilitarian, socialstatus, species')


#defining background knowledge as non definite Horn clauses
background_know = [Implies(fitness & gender, False), Implies(fitness  & age, False),
                  Implies(fitness & utilitarian, False), Implies(fitness & socialstatus, False),
                  Implies(fitness & species, False), Implies(gender & age, False),
                  Implies(gender & utilitarian, False), Implies(gender & socialstatus, False), 
                  Implies(gender & species, False), Implies(age & utilitarian, False), 
                  Implies(age & socialstatus, False), Implies(age & species, False), 
                  Implies(utilitarian &  socialstatus, False), Implies(utilitarian & species, False),
                  Implies(socialstatus & species, False), Implies(saved & not_saved, False),
                  Implies(female & male, False), Implies(old & young, False), 
                  Implies(more & less, False), Implies(low & high, False), 
                  Implies(humans & pets, False), Implies(fit & fat, False), 
                  Implies(green & red, False), Implies(france & not_france, False),
                  Implies(india & not_india, False), Implies(norway & not_norway, False),
                  Implies(east & not_east, False), Implies(west & not_west, False), 
                  Implies(south & not_south, False)
                  ]


# ## Apply Algorithm on dataset

# We can use any set of countries and add background knowledge of countries accordingly to find a common ground for countries' dataset.

# In[ ]:


start = time.time()

find_common_ground(horn_expression, background_know, background_know_2, collection_of_symbols)

end = time.time()

print("The time of execution of above program is :",
      (end-start) * 10**3, "ms")

