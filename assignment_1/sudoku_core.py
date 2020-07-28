import numpy as np
from pysat.formula import CNF
from pysat.solvers import MinisatGH
from ortools.sat.python import cp_model
import gurobipy as gp
from gurobipy import GRB
import clingo
from clingo import Number

###
### Propagation function to be used in the recursive sudoku solver
###
def propagate(sudoku_possible_values,k):
    # generating a list of lists, containing the indexes of the cells in the blocks of the sudoku
    # this will later be used to get the indexes of cells of the same block
    blocks = []
    digits = list(range(0, k ** 2 ))
    for i in range(0, k):
        block=[]
        for j in range(0,k):
            block.append(digits[0])
            del digits[0]
        blocks.append(block)

    # if a cell contains only one value, meaning that that value is filled in, we can remove this value
    # from the corresponding cells in the same row, column and block
    for i in range(k**2):
        for j in range(k**2):
            if len(sudoku_possible_values[i][j]) == 1:

                #remove value from all cells in row
                for index_row in range(k**2):
                    if index_row != j and sudoku_possible_values[i][j][0] in sudoku_possible_values[i][index_row]:
                        if len(sudoku_possible_values[i][index_row]) > 1:
                            sudoku_possible_values[i][index_row].remove(sudoku_possible_values[i][j][0])

                #remove value from all cells in column
                for index_column in range(k**2):
                    if index_column != i and sudoku_possible_values[i][j][0] in sudoku_possible_values[index_column][j]:
                        if len(sudoku_possible_values[index_column][j]) > 1:
                            sudoku_possible_values[index_column][j].remove(sudoku_possible_values[i][j][0])

                # getting the indexes of the block of the current cell (sudoku_possible_values[i][j])
                for block in blocks:
                    if i in range(block[0], block[-1]+1):
                        block_row_start = block[0]
                        block_row_end = block[-1]
                    if j in range(block[0], block[-1]+1):
                        block_column_start = block[0]
                        block_column_end = block[-1]

                # remove value from all cells in block
                for r in range(block_row_start, block_row_end+1):
                    for c in range(block_column_start, block_column_end+1):
                        if sudoku_possible_values[i][j][0] in sudoku_possible_values[r][c] and \
                                len(sudoku_possible_values[r][c]) > 1:
                            sudoku_possible_values[r][c].remove(sudoku_possible_values[i][j][0])

    return sudoku_possible_values;


# function that returns a list of all the edges of the sudoku
def make_edges(k):
    # generating an array containing the number of the cells
    list_vertices = list(range(1, (k**2)*(k**2)+1))
    vertice_list = []
    for i in range(k**2):
        vertice_list.append(list_vertices[:k**2])
        del list_vertices[:k**2]
    array_vertices = np.asarray(vertice_list)

    # generating a list of lists, containing the indexes of the cells in the blocks of the sudoku
    # this will later be used to get the indexes of cells of the same block
    digits = list(range(0, k ** 2))
    blocks = []
    for i in range(0, k):
        block=[]
        for j in range(0,k):
            block.append(digits[0])
            del digits[0]
        blocks.append(block)

    # creating edges
    edges = []
    for i in range(k**2):
        for j in range(k**2):
            #adding edge for the cell with all cells in the same row
            for index_row in range(k ** 2):
                if index_row != j:
                    edges.append((array_vertices[i, j], array_vertices[i, index_row]))
            # adding edge for the cell with all cells in the same column
            for index_column in range(k ** 2):
                if index_column != i:
                    edges.append((array_vertices[i, j], array_vertices[index_column, j]))

            # getting the indexes of the block of the current cell
            for block in blocks:
                if i in range(block[0], block[-1]):
                    block_row_start = block[0]
                    block_row_end = block[-1]
                if j in range(block[0], block[-1]):
                    block_column_start = block[0]
                    block_column_end = block[-1]

            # flattend block
            block = array_vertices[block_row_start:block_row_end+1, block_column_start:block_column_end+1].flatten()

            # adding edge for the cell with all cells in the same block
            for b in range(k**2):
                if array_vertices[i, j] != block[b]: edges.append((array_vertices[i, j], block[b]))

    # remove duplicate edges
    edges_sorted=[]
    for x in edges:
        edges_sorted.append(tuple(sorted(x)))
    edges = list(set(edges_sorted))
    return edges


# function that returns an integer number as unique index of the combination of the cell number and the digit value
def var_number(i, d, num_digits):
    return int(((i - 1) * num_digits) + d);

###
### Solver that uses SAT encoding
###
def solve_sudoku_SAT(sudoku,k):
    # creating the formula for the SAT solver
    formula = CNF();

    # creating a sudoku array with individual vertice numbers
    num_vertices = k**4
    list_vertices = list(range(1, (k**2)*(k**2)+1))
    vertice_list = []
    for i in range(k**2):
        vertice_list.append(list_vertices[:k**2])
        del list_vertices[:k**2]
    array_vertices = np.asarray(vertice_list)

    # generating the edges
    edges = make_edges(k)

    # filling in the formula with clauses
    # adding the clauses for every cell containing a unique index for every value
    num_digits = k ** 2
    for i in range(1, num_vertices+1):
        clause = [];
        for d in range(1, num_digits + 1):
            clause.append(var_number(i,d, num_digits))
        formula.append(clause);

    # adding the clause that every cell can only contain one value
    for i in range(1, num_vertices + 1):
        for c1 in range(1, num_digits + 1):
            for c2 in range(c1 + 1, num_digits + 1):
                clause = [-1 * var_number(i, c1, num_digits), -1 * var_number(i, c2, num_digits)];
                formula.append(clause);

    #adding the clauses that edges cannot contain the same value
    for (i, j) in edges:
        for d in range(1, num_digits+1):
            clause = [int(-var_number(i, d, num_digits)), int(-var_number(j, d, num_digits))]
            formula.append(clause)

    # adding the clauses that contain the true values for the cells which we are certain about (that are already filled in)
    for i in range(k ** 2):
        for j in range(k ** 2):
            if sudoku[i][j] != 0:
                clause = [int(var_number(array_vertices[i, j], sudoku[i][j], num_digits))]
                formula.append(clause)



    # creating sat solver and checking for an answer
    solver = MinisatGH();
    solver.append_formula(formula);
    answer = solver.solve();

    # check if sudoku is solvable and fill in sudoku and return sudoku, otherwise return None
    if answer == True:
        model = solver.get_model();
        sudoku = array_vertices
        for i in range(k**2):
            for j in range(k**2):
                for d in range(1, k**2+1):
                    if var_number(array_vertices[i,j],d ,num_digits) in model:
                        sudoku[i, j] = d
                        break
        sudoku = sudoku.tolist()
        return sudoku
    else:
        return None

###
### Solver that uses CSP encoding
###
def solve_sudoku_CSP(sudoku,k):
    # creating a sudoku array with individual vertice numbers
    num_vertices = (k ** 2) * (k ** 2)
    list_vertices = list(range(1, (k ** 2) * (k ** 2) + 1))
    vertice_list = []
    for i in range(k ** 2):
        vertice_list.append(list_vertices[:k ** 2])
        del list_vertices[:k ** 2]
    array_vertices = np.asarray(vertice_list)

    #generating edges
    edges = make_edges(k)

    model = cp_model.CpModel();

    # creating the domain for every cell
    num_digits = k**2
    vars = dict()
    for i in range(1, num_vertices+1):
        vars[i] = model.NewIntVar(1, num_digits, "x{}".format([i]))

    # filling in the values for every cell if they are filled in in the sudoku
    for i in range(k**2):
        for j in range(k**2):
            if sudoku[i][j] != 0:
                vars[array_vertices[i,j]] = model.NewIntVar(sudoku[i][j],sudoku[i][j], "x{}".format([array_vertices[i,j]]))

    # adding constraints that edges cannot have the same digit
    for (i,j) in edges:
        model.Add(vars[i] != vars[j]);

    # creating csp solver and checking for an answer
    solver = cp_model.CpSolver();
    answer = solver.Solve(model);

    # check if sudoku is solvable and fill in sudoku and return sudoku, otherwise return None
    if answer == cp_model.FEASIBLE:
        sudoku = array_vertices
        for i in range(k**2):
            for j in range(k**2):
                sudoku[i][j] = solver.Value(vars[sudoku[i][j]])
        sudoku = sudoku.tolist()
        return sudoku
    else:
        return None;

###
### Solver that uses ASP encoding
###
def solve_sudoku_ASP(sudoku,k):
    # generating asp_code
    asp_code = "";

    # adding all vertices to the asp code
    list_vertices = list(range(1, (k ** 2) * (k ** 2) + 1))
    for i in range(len(list_vertices)):
        asp_code += """vertex({}).""".format(list_vertices[i])

    # creating a sudoku array with individual vertice numbers
    vertice_list = []
    for i in range(k**2):
        vertice_list.append(list_vertices[:k**2])
        del list_vertices[:k**2]
    array_vertices = np.asarray(vertice_list)

    # generating edges
    edges = make_edges(k)

    # adding edge to the asp code
    for i in range(len(edges)):
        asp_code+="""edge({},{}).""".format(edges[i][0],edges[i][1])

    # # adding rules that contain information that every cell can only contain 1 digit
    list_digits = list(range(1,k**2+1))
    new_line_to_check = ""
    for i in range(len(list_digits)):
        string_to_code = "digit(C,{}) :- vertex(C)".format(list_digits[i])
        for j in range(len(list_digits)):
            if i!=j:
                string_to_code+=", not digit(C,{})".format(list_digits[j])
        asp_code+=string_to_code+"."
        new_line_to_check+=string_to_code+"."

    # adding rule that edges cannot contain the same number
    asp_code += """
        :- edge(V1,V2), digit(V1,X), digit(V2,X).
    """

    # filling in the values for the cells that are filled in already
    for i in range(k**2):
        for j in range(k**2):
            if sudoku[i][j] !=0:
                asp_code += """
                        digit({},{}).
                    """.format(array_vertices[i][j],sudoku[i][j])

    # creating asp solver and checking for an answer
    control = clingo.Control();
    control.add("base", [], asp_code);
    control.ground([("base", [])])

    # saving the results in a list, so if there is a solution we can use the results to fill in the sudoku
    results = []
    def on_model(model):
        for atom in model.symbols(atoms=True, shown=True):
            if atom.name == 'digit':
                results.append(atom.arguments)
        model.symbols(shown=True);

    control.configuration.solve.models = 1;
    answer = control.solve(on_model=on_model)

    # check if sudoku is solvable and fill in sudoku and return sudoku, otherwise return None
    if answer.satisfiable == True:
        sudoku=array_vertices
        for i in range(k**2):
            for j in range(k**2):
                value = [r[1] for r in results if r[0]==Number(array_vertices[i][j])][0].number
                sudoku[i][j]=value
        sudoku = sudoku.tolist()
        return sudoku
    else:
        return None;

###
### Solver that uses ILP encoding
###
def solve_sudoku_ILP(sudoku,k):
    # generating ILP model
    model = gp.Model();

    # generating edges
    edges = make_edges(k)

    # creating a sudoku array with individual vertice numbers
    list_vertices = list(range(1, (k ** 2) * (k ** 2) + 1))
    vertice_list = []
    for i in range(k ** 2):
        vertice_list.append(list_vertices[:k ** 2])
        del list_vertices[:k ** 2]
    array_vertices = np.asarray(vertice_list)

    num_digits = k**2
    v={}
    for i in range(k**2):
        for j in range(k**2):
            if sudoku[i][j] == 0:
                for d in range(1, num_digits + 1):
                    v[(array_vertices[i,j], d)] = model.addVar(vtype=GRB.BINARY, name="x({},{})".format(array_vertices[i,j], d))
            else:
                for d in range(1, num_digits + 1):
                    if sudoku[i][j] == d:
                        v[(array_vertices[i,j], d)] = model.addVar(vtype=GRB.BINARY, obj=1, name="x({},{})".format(array_vertices[i,j], d))
                    else:
                        v[(array_vertices[i,j], d)] = model.addVar(vtype=GRB.BINARY, ub=0, name="x({},{})".format(array_vertices[i,j], d))

    # adding constraint that every cell contains only at least one and at most one value
    for i in range(1, k**4+1):
        model.addConstr(gp.quicksum([v[(i,d)] for d in range(1, num_digits+1)]) == 1)

    # adding constraints that edges cannot have the same digit
    for (i,j) in edges:
        for d in range(1, num_digits+1):
            model.addConstr(v[(i,d)] + v[(j, d)] <=1)

    # optimize model and try and find solution
    model.optimize();

    # check if sudoku is solvable and fill in sudoku and return sudoku, otherwise return None
    if model.status == GRB.OPTIMAL:
        sudoku=array_vertices
        for i in range(k**2):
            for j in range(k**2):
                for d in range(1,num_digits+1):
                    if v[(sudoku[i][j],d)].x == 1:
                        sudoku[i][j] = d
                        break
        sudoku = sudoku.tolist()
        return sudoku
    else:
        return None;
