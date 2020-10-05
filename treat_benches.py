import csv
import matplotlib.pyplot as plt


def number_solved_in_less_than(data, prover_name, bench_name, maxtime):
    return([ len([ row for row in data if int(row['time'])<i and row['prover'].strip()==prover_name and row['result'].strip()=="Proved" and bench_name in row['file']]) for  i in range(1,maxtime)])

def number_of_benches(data, list_of_provers, bench_name):
    l=[len([row for row in data if row['prover'].strip()==prover_name and bench_name in row['file']]) for prover_name in list_of_provers]
    if min(l) != max(l):
        print("Warning not same number of benches for all provers !")
        return(max(l))
    else:
        return(max(l))
    

def generate_graph(filename, list_of_provers_colors, bench_directory, bench_display_name, maxtime):
    for (prover_name,color_name) in list_of_provers_colors:
        plt.plot(range(1,maxtime), number_solved_in_less_than(data, prover_name, bench_directory, maxtime), color=color_name, label = prover_name)
    plt.ylim(1,number_of_benches(data, map(lambda x:x[0],list_of_provers_colors), bench_directory)+5) 
    plt.xlim(1,maxtime) 
    plt.xlabel('time') 
    plt.ylabel('number of problem solved') 
    plt.title('Results on ' + bench_display_name) 
    plt.legend() 
    plt.savefig(filename)
    plt.show()    

with open('data2.csv') as csvfile:
    reader = csv.DictReader(csvfile, delimiter=';')
    data= list( row for row in reader)
    generate_graph("col-trans-graph.pdf", [("CLprover","red"),("vampire","green"),("eprover","darkred"),("zenon","darkblue"),("nanocop","orange"),("leancop","pink"),("ChewTPTP","purple")], "col-trans", "Col transitivity", 100)
    generate_graph("euclid-graph.pdf", [("vampire","green"),("eprover","red")], "euclid", "Euclid", 100)
    
