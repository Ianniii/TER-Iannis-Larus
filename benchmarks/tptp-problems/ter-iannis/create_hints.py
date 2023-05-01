import os
from os import listdir
import re
import sys
import shutil

# Les arguments pour lancer la commande sont : 
# le nom du fichier 
# le chemin vers le dossier qui contient tous les fichiers geocoq
# le chemin vers le dossier qui contient tous les fichiers larus
# le dossier destination (en crée un s'il n'existe pas)
# Optionnel : 
# Exemple : python3 ./create_hint2.py ./geo ./lar ./new_folder [8]


######### Mettre cette variable à 1 pour avoir le fichier geocoq dans le dossier pour chaque lemme #########
CREATE_GEO_FILE = 0

def main() :
    steps = 4
    arg = sys.argv

    if(len(arg) == 5):
        steps = int(arg[4])

    elif(len(arg) != 4):
        print("Il faut en argument  : le fichier python, le chemin du fichier GeoCoq, le chemin du fichier Larus à modifier et le chemin du répertoire vers lequel vous voulez mettre vos fichiers. \n")
        exit(0)
    
    path_geo = arg[1]
    if(path_geo[-1]!='/'):
        path_geo += '/'

    path_lar = arg[2]
    if(path_lar[-1]!='/'):
        path_lar += '/'
    file_lar = listdir(path_lar)

    path_results = arg[3]
    if(path_results[-1]!='/'):
        path_results += '/'

    # Crée le dossier de résultats s'il n'existe pas
    if not os.path.exists(path_results):
        os.mkdir(path_results)
    
    for proof in file_lar:
        size = len(proof)
        try:
            index = proof.index("_")
            name_file = proof[index+1:size-2]
        except ValueError:
            name_file = proof[:size-2]

        # print("#######\n" + name_file + "\n#######\n")
        
        # Chemin des fichiers Geocoq et Larus
        path_file_geo = path_geo + name_file + ".v"
        path_file_lar = path_lar + proof

        create_hint(path_file_geo, path_file_lar, path_results, name_file, steps)
        


def create_hint(filein, fileout, folder_new, name_file, steps):
    if (not os.path.exists(filein)):

        print("Mauvais chemin pour fichier de lecture pour " + filein + "\n")
        return

    if (not os.path.exists(fileout)):
        print("Mauvais chemin pour le fichier d'écriture pour " + fileout + "\n")
        return
    
    path_file = folder_new + name_file+ '/'
    if not os.path.exists(path_file):
        os.mkdir(path_file)
    
    if(CREATE_GEO_FILE):
        shutil.copy(fileout, path_file + name_file + ".v")

    fileout = shutil.copy(fileout, path_file + name_file + "_base.p")

    fichier = open(filein, "r")
    lines = fichier.readlines()
    fichier.close()

    (lines_exist,lines_prop,lines_steps) = detect_hints(lines, steps)

    (facts_exist,lemmas_exist) = extract_lemma(lines_exist)
    (facts_prop,lemmas_prop) = extract_lemma(lines_prop)
    (facts_steps,lemmas_steps) = extract_lemma(lines_steps)

    write_hints(filein, fileout, path_file, name_file + "_exist", facts_exist, lemmas_exist)
    write_hints(filein, fileout, path_file, name_file + "_prop", facts_prop, lemmas_prop)
    write_hints(filein, fileout, path_file, name_file + "_steps" + str(steps), facts_steps, lemmas_steps)

    return 0



# Récupère les lignes dans lequel on crée un point dans la preuve GeoCoq
def detect_hints(lines, steps):
    tab_lemmas = []
    tab_proposition = []
    tab_steps = []
    count = 0

    for line in lines:
        line_s = line.strip()

        if "Tf:exists" in line_s:
            tab_lemmas.append(line_s)

        if "conclude proposition" in line_s:
            tab_proposition.append(line_s)
        
        if "assert" in line_s:
            count += 1
            if(count == steps):
                tab_steps.append(line_s)
                count = 0

    return (tab_lemmas, tab_proposition, tab_steps)



# Recupère le nom du lemme utilisé aux lignes qui créent des points
def extract_lemma(lines):
    tab_lemmas = []
    tab_facts = []
    lemma_line = []

    # Find lemma in GeoCoq
    for line in lines:
        line_axiom = line.strip()
        #print(line_axiom)

        word = "\([\s\w\\\/\:\,\~]*\)"
        for match in re.finditer(word, line_axiom):
            #print(line_axiom[match.start()+1:match.end()-1])
            lemma_line.append(line_axiom[match.start()+1:match.end()-1])
        
        if("Tf:exists" in lemma_line[0]):
            index = lemma_line[0].index(",")
            lemma_line[0] = lemma_line[0][index+2:]

        tab_facts.append(lemma_line[0])

        if(len(lemma_line) == 2):
            if("conclude_def" in lemma_line[1]):
                tab_lemmas.append("")

            else:

                index = lemma_line[1].find(" ")
                lemma_line[1] = lemma_line[1][index+1:]

                size = len(lemma_line[1])
                if(lemma_line[1][size-1] == ' '):
                    lemma_line[1] = lemma_line[1][:size-1]
                tab_lemmas.append(lemma_line[1])

        lemma_line = []
    return (tab_facts,tab_lemmas)


def nb_arg(fileout, tab_lemmas):

    #print(tab_lemmas)
    if(tab_lemmas == []):
        return ([],[])
    name_lemmas = []
    lemmas = []
    args = []
    file = open(fileout, "r")

    # Cherche les lemmes utilisés dans le .p
    for line in file.readlines():
        lemma = line.strip()
        for i in range (len(tab_lemmas)):
            name_lemma = tab_lemmas[i] + ','
            if ((name_lemma in lemma) and (tab_lemmas[i]!="" )):
                # print(tab_lemmas[i])
                name_lemmas.append(tab_lemmas[i])
                lemmas.append(lemma)

    for i in range (len(lemmas)):
        count = 0
        word = "\[[a-zA-Z,]*\]"
        for match in re.finditer(word, lemmas[i]):
            chaine = lemmas[i][match.start():match.end()]
            count += len(re.findall(',', chaine)) + 1
        
        args.append(count)

    return (name_lemmas,args)

def create_facts(filein, facts):
    arg_c = arg_conjecture(filein)
    args = []

    for i in range (len(facts)):
        args.append(predic_to_hint(arg_c, facts[i]))
    
    return args

def predic_to_hint(arg_conjecture, pred):
    arg_exist = []
    elements = []
    ascii_value = 65
    hint = "("
    # Si True, prochain mot récupéré avant un espace et le nom du lemme
    name_pred = True
    # Afin de placer correctement les virgules pour l'écriture des prédicats
    first_arg = True
    #Condition d'arrêt de la fonction lorsqu'il n'y a plus d'occurences d'espace
    stop = False
    isNot = False

    while (not stop):
        # Chercher l'emplacement du prochain espace
        try:
            index = pred.index(" ")
            texte = pred[:index]
        except ValueError:
            texte = pred[:]
            stop = True


        # Cas où le mot est le nom du lemme
        if(texte == "~"):
            hint = hint + texte + '('
            isNot = True
        
        elif(name_pred):
            name_pred = False
            texte = texte[0].lower() + texte[1:]
            hint = hint + texte + '('
        
        # Cas du "ou"/"et" logique
        elif(texte =="/\\" or texte == "\\/"):
            if texte[0]=='/':
                texte = " & "
            else:
                texte = " | "
            
            if(isNot):
                hint += ")"
                isNot = False
            hint = hint + ") " + texte
            name_pred = True
            first_arg = True

        # Cas où le mot est un point utilisé pour un lemme
        else:

            try:
                num = arg_conjecture.index(texte)
            except ValueError:
                try:
                    pos = arg_exist.index(texte)
                except ValueError:
                    char = chr(ascii_value)
                    arg_exist.append(texte)
                    elements.append(char)
                    pos = len(arg_exist)-1
                    ascii_value += 1
                
                num = elements[pos]

            if not first_arg:
                hint = hint + ','
            else:
                first_arg = False
            hint = hint + str(num)

        pred = pred[index+1:]

    if(isNot):
        hint += ")"

    hint = hint +"))"

    print(elements)
    return hint
    


def arg_conjecture(filein):

    file = open(filein, "r")
    texte = file.read()
    word = "forall .*,"

    # Enlève le forall et la virgule à la fin
    for match in re.finditer(word, texte):
        texte = texte[match.start()+7:match.end()-1]
    
    index = 0
    arg = []

    # Reste dans la boucle jusqu'à ce qu'il n'y ait plus d'espaces
    while(1):
        try:
            index = texte.index(" ")
            arg.append(texte[0:index])
            texte = texte[index+1:]
        except ValueError:
            arg.append(texte)
            break
    
    return arg


def write_hints(filein, fileout, path_file, name_file, facts, lemmas):
    args_facts = create_facts(filein, facts)
    if(len(args_facts)>0):
        file_facts = shutil.copy(fileout, path_file + name_file + "_facts.p")
        file_facts = open(file_facts, "a")
        write_facts(file_facts, args_facts)

    (name_lemmas,count) = nb_arg(fileout, lemmas)
    if(len(name_lemmas)>0):
        file_lemmas = shutil.copy(fileout, path_file + name_file + "_lemmas.p")
        file_lemmas = open(file_lemmas, "a")
        write_lemmas(file_lemmas, name_lemmas, count)

        

def write_lemmas(file, name_lemmas, count):
    file.write("\n\n%%% HINTS %%% \n\n")

    # Création hints avec lemmas
    for i in range (len(name_lemmas)):
        hint = "fof(hintname" + str(i) +", hint, _, _, " + name_lemmas[i] +"("

        for j in range (count[i]):
            if(j != count[i]-1):
                hint = hint + "_," 
            else:
                hint = hint + "_)).\n"

        if(count[i]>0):
            file.write(hint)
    file.close()


def write_facts(file, args_facts):
    file.write("\n\n%%% HINTS %%% \n\n")

    k = 0
    # Création hints avec facts
    word = "[\w\~][\w\(\,\)]*[\)]"
    for i in range (len(args_facts)):
        for match in re.finditer(word, args_facts[i]):
            fact = args_facts[i][match.start():match.end()]

            if(("neq" in fact) or fact[1].isupper()):
                continue

            error = fact.count(')') - fact.count('(')
            fact = fact[:len(fact)-error]
                
            hint = "fof(hintname" + str(k) +", hint, " + fact + ", _, _).\n"
            file.write(hint)
            k+=1

    file.close()

main()
