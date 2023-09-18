import heapq
import time

from hitman import HC, HitmanReferee
from pprint import pprint
from typing import List, Tuple, Dict, Optional, Callable
from itertools import combinations
from reso_SAT import *

# alias de types
Grid = List[List[int]]
PropositionnalVariable = int
Literal = int
Clause = List[Literal]
ClauseBase = List[Clause]

# Variables globales
nbVar = len(HC)
nbVar_reel = 0
m = 0  # lignes
n = 0  # colonnes
liste_de_clauses: List[Clause] = []
hr = HitmanReferee()


# ------------------- DEBUT GESTION PHASE 1 -------------------


def remove_duplicates(cb) -> ClauseBase:
    unique_cb = set(tuple(sublist) for sublist in cb)
    return [list(sublist) for sublist in unique_cb]


def at_least_n(n: int, variables: List[int]) -> List[Clause]:
    clauses = []
    for comb in combinations(variables, len(variables) - (n - 1)):
        clauses.append(list(comb))
    return clauses


def at_most_n(n: int, variables: List[int]) -> List[Clause]:
    clauses = []
    vars_neg = [i * -1 for i in variables]
    for comb in combinations(vars_neg, n + 1):
        clauses.append(list(comb))
    return clauses


def exactly_n(n: int, variables: List[int]) -> List[Clause]:
    if not variables:
        return []
    if n == 0:
        return at_most_n(0, variables)
    if n == len(variables):
        return at_least_n(n, variables)
    clauses = at_most_n(n, variables)
    clauses += at_least_n(n, variables)
    return clauses


# Transforme notre triplet représentant nos cas avec leur variables en une variable propositionnelle
def cell_to_variable(i: int, j: int, val: int) -> PropositionnalVariable:
    return (i * nbVar * m) + (j * nbVar) + val + 1


# Transforme notre variable propositionnelle en un tuple de 3 entiers
def variable_to_cell(var: PropositionnalVariable) -> Tuple[int, int, int]:
    return (
        (var - 1) // (m * nbVar),
        ((var - 1) % (m * nbVar)) // nbVar,
        (var - 1) % nbVar,
    )


# retourne l'ensemble des variables booléennes représentant une case de la grille
def cellVariables(i: int, j: int) -> List[PropositionnalVariable]:
    cellVariables = []
    for v in range(nbVar):
        cellVariables.append(cell_to_variable(i, j, v))
    return cellVariables


def initialize_regles(status, map) -> ClauseBase:
    liste_clauses = []

    # Règle 1: une variable par case max
    clauses_regle1 = []
    for i in range(n):
        for j in range(m):
            clauses_regle1 += exactly_n(1, cellVariables(i, j))

    # Règle 2: il y a exactement 1 costume, 1 corde de piano et 1 cible
    liste_suit = []
    liste_piano = []
    liste_cible = []
    clauses_regle2 = []
    for i in range(n):
        for j in range(m):
            liste_suit.append(cell_to_variable(i, j, (HC.SUIT.value - 1)))
            liste_piano.append(cell_to_variable(i, j, (HC.PIANO_WIRE.value - 1)))
            liste_cible.append(cell_to_variable(i, j, (HC.TARGET.value - 1)))

    clauses_regle2 += exactly_n(1, liste_suit)
    clauses_regle2 += exactly_n(1, liste_piano)
    clauses_regle2 += exactly_n(1, liste_cible)

    # Règle 3: la case de départ est toujours vide
    i = status["position"][0]
    j = status["position"][1]
    map[(i, j)] = HC.EMPTY

    liste_clauses.append([cell_to_variable(i, j, HC.EMPTY.value - 1)])
    liste_clauses += clauses_regle1
    liste_clauses += clauses_regle2

    return liste_clauses


# Fonction de gestion de l'information donnée par l'écoute à chaque déplacement
def gestion_bruit(status) -> ClauseBase:
    # les positions commencent à 0
    position_i = status["position"][0]
    position_j = status["position"][1]

    # Chercher les cases concernées par l'écoute
    liste_cases_environnantes = []

    for i in range(position_i - 2, position_i + 3):
        for j in range(position_j - 2, position_j + 3):
            # On ne prend pas en compte les cases hors plateau
            # Ainsi que la case sur laquelle on est
            if (
                (i != position_i or j != position_j)
                and (i >= 0 and j >= 0)
                and (i < n and j < m)
            ):
                # On ne s'intéresse qu'aux variables concernant les gardes et les civils
                for k in range(HC.GUARD_N.value - 1, HC.CIVIL_W.value):
                    liste_cases_environnantes.append(cell_to_variable(i, j, k))

    bruit = status["hear"]
    liste_clauses = []
    # Notre limite de base c'est 3
    if bruit < 2:
        liste_clauses += exactly_n(bruit, liste_cases_environnantes)

    return liste_clauses


def gestion_vision(status) -> ClauseBase:
    liste_clauses = []
    vision = status["vision"]
    for info in vision:
        # pour chaque case connue grâce à la vision
        pos_i = info[0][0]
        pos_j = info[0][1]
        val = info[1].value - 1
        x = [cell_to_variable(pos_i, pos_j, val)]
        liste_clauses.append(x)
    return liste_clauses


def demande(pos_i, pos_j, orientation, map) -> Tuple[bool, bool, int, int]:
    # orientations = [HC.N,HC.E,HC.S,HC.W]
    anyguard = [HC.GUARD_N, HC.GUARD_E, HC.GUARD_W, HC.GUARD_S]
    liste_clauses = []
    liste_clauses_intermediaire = []
    offset_vision = []
    offsets = []

    offset_N = []
    offset_S = []
    offset_E = []
    offset_W = []
    blocking_items = [
        HC.CIVIL_N,
        HC.CIVIL_S,
        HC.CIVIL_E,
        HC.CIVIL_W,
        HC.WALL,
        HC.GUARD_N,
        HC.GUARD_S,
        HC.GUARD_E,
        HC.GUARD_W,
        HC.SUIT,
        HC.PIANO_WIRE,
    ]

    # Les valeurs de retour après le booléen sont: 2 si hors map, 1 si garde ou mur sur la case, 0 sinon

    if orientation == HC.E:
        offset_N = [(1, 1), (1, 2), (1, 3)]
        offset_S = [(1, -1), (1, -2), (1, -3)]
        offset_E = [(2, 0), (3, 0), (4, 0)]
        offset_W = [(0, 0), (-1, 0), (-2, 0)]

        # On vérifie qu'on ne veut pas aller en dehors de la map
        if pos_i + 1 >= n:
            return False, False, 2, -1  # 2 code erreur index

        # Vérification qu'il n'y a pas de garde ni de mur sur la case où on veut aller
        for elem in anyguard:
            if (
                map[(pos_i + 1, pos_j)] == elem or map[(pos_i + 1, pos_j)] == HC.WALL
            ):  # si on veut aller sur une case où il y a un garde ou un mur
                return (
                    False,
                    False,
                    1,
                    -1,
                )  # Pas safe et 1 pour dire qu'il y a un mur ou un garde

        offsets = [
            (2, 0, HC.GUARD_W.value - 1),
            (3, 0, HC.GUARD_W.value - 1),
            (1, 1, HC.GUARD_S.value - 1),
            (1, 2, HC.GUARD_S.value - 1),
            (1, -1, HC.GUARD_N.value - 1),
            (1, -2, HC.GUARD_N.value - 1),
        ]

    elif orientation == HC.N:
        offset_N = [(0, 2), (0, 3), (0, 4)]
        offset_S = [(0, 0), (0, -1), (0, -2)]
        offset_E = [(1, 1), (2, 1), (3, 1)]
        offset_W = [(-1, 1), (-2, 1), (-3, 1)]
        # calcul des offsets si la case où on veut aller est en haut
        # offset_vision = [(0,2),(0,3),(0,4),(1,1),(2,1),(3,1),(-1,1),(-2,1),(-3,1),(0,0),(0,-1),(0,-2)]

        # On vérifie qu'on ne veut pas aller en dehors de la map
        if pos_j + 1 >= m:
            return False, False, 2, -1  # 2 code erreur index

        # Vérification qu'il n'y a pas de garde ni de mur sur la case où on veut aller
        for elem in anyguard:
            if (
                map[(pos_i, pos_j + 1)] == elem or map[(pos_i, pos_j + 1)] == HC.WALL
            ):  # si on veut aller sur une case où il y a un garde ou un mur
                return (
                    False,
                    False,
                    1,
                    -1,
                )  # Pas safe et 1 pour dire qu'il y a un mur ou un garde

        offsets = [
            (-1, 1, HC.GUARD_E.value - 1),
            (-2, 1, HC.GUARD_E.value - 1),
            (0, 2, HC.GUARD_S.value - 1),
            (0, 3, HC.GUARD_S.value - 1),
            (1, 1, HC.GUARD_W.value - 1),
            (2, 1, HC.GUARD_W.value - 1),
        ]

    elif orientation == HC.W:
        # On vérifie qu'on ne veut pas aller en dehors de la map
        if pos_i - 1 < 0:
            return False, False, 2, -1  # 2 code erreur index

        # calcul des offsets si la case où on veut aller est à gauche
        offset_N = [(-1, 1), (-1, 2), (-1, 3)]
        offset_S = [(-1, -1), (-1, -2), (-1, -3)]
        offset_E = [(0, 0), (1, 0), (2, 0)]
        offset_W = [(-2, 0), (-3, 0), (-4, 0)]

        # print(offset_vision)
        # offset_vision = [(-2,0),(-3,0),(-4,0),(-1,1),(-1,2),(-1,3),(-1,-1),(-1,-2),(-1,-3),(0,0),(1,0),(2,0)]

        # Vérification qu'il n'y a pas de garde ni de mur sur la case où on veut aller
        for elem in anyguard:
            if (
                map[(pos_i - 1, pos_j)] == elem or map[(pos_i - 1, pos_j)] == HC.WALL
            ):  # si on veut aller sur une case où il y a un garde ou un mur
                return (
                    False,
                    False,
                    1,
                    -1,
                )  # Pas safe et 1 pour dire qu'il y a un mur ou un garde

        offsets = [
            (-1, 0, HC.GUARD_W.value - 1),
            (-2, 0, HC.GUARD_W.value - 1),
            (-1, 1, HC.GUARD_S.value - 1),
            (-1, 2, HC.GUARD_S.value - 1),
            (-1, -1, HC.GUARD_N.value - 1),
            (-1, -2, HC.GUARD_N.value - 1),
        ]

    elif orientation == HC.S:
        # calcul des offsets si la case où on veut aller est en bas
        # offset_vision = [(0,-2),(0,-3),(0,-4),(-1,-1),(-2,-1),(-3,-1),(1,-1),(2,-1),(3,-1),(0,0),(0,1),(0,2)]
        offset_N = [(0, 0), (0, 1), (0, 2)]
        offset_S = [(0, -2), (0, -3), (0, -4)]
        offset_E = [(1, -1), (2, -1), (3, -1)]
        offset_W = [(-1, -1), (-2, -1), (-3, -1)]

        # offset_vision = [(0,-2),(0,-3),(0,-4),(-1,-1),(-2,-1),(-3,-1),(1,-1),(2,-1),(3,-1),(0,0),(0,1),(0,2)]
        # On vérifie qu'on ne veut pas aller en dehors de la map
        if pos_j - 1 < 0:
            return False, False, 2, -1  # 2 code erreur index

        # Vérification qu'il n'y a pas de garde ni de mur sur la case où on veut aller
        for elem in anyguard:
            if (
                map[(pos_i, pos_j - 1)] == elem or map[(pos_i, pos_j - 1)] == HC.WALL
            ):  # si on veut aller sur une case où il y a un garde ou un mur
                return (
                    False,
                    False,
                    1,
                    -1,
                )  # Pas safe et 1 pour dire qu'il y a un mur ou un garde

        offsets = [
            (-1, -1, HC.GUARD_E.value - 1),
            (-2, -1, HC.GUARD_E.value - 1),
            (0, -2, HC.GUARD_S.value - 1),
            (0, -3, HC.GUARD_S.value - 1),
            (1, -1, HC.GUARD_W.value - 1),
            (2, -1, HC.GUARD_W.value - 1),
        ]

    # ---------- GESTION VISION POTENTIEL --------- #

    # -- On évite notamment d'ajouter le gain potentiel de quelque chose derrière un mur (qu'on ne pourra pas voir du coup)
    offsets_vision_orientation = [offset_N, offset_S, offset_W, offset_E]

    flag1 = False
    for type_offset in offsets_vision_orientation:
        # print(type_offset)
        for offset in type_offset:
            if (0 <= offset[0] + pos_i < n) and (0 <= offset[1] + pos_j < m):
                # print("AVANT : ", offset[0] + pos_i, offset[1] + pos_j)
                if (
                    map[(offset[0] + pos_i, offset[1] + pos_j)] not in blocking_items
                    and map[(offset[0] + pos_i, offset[1] + pos_j)] == 0
                    and offset not in offset_vision
                ):
                    # print("APRES : ", offset[0] + pos_i, offset[1] + pos_j)
                    offset_vision.append(offset)
                else:
                    # print("APRES : ", offset[0] + pos_i, offset[1] + pos_j)
                    if map[(offset[0] + pos_i, offset[1] + pos_j)] in blocking_items:
                        # print("break")
                        flag1 = True
                        break
    # print(offset_vision)
    # ---------- GESTION VISION DES GARDES --------- #
    for elem in offsets:
        if (0 <= elem[0] + pos_i < n) and (0 <= elem[1] + pos_j < m):
            liste_clauses_intermediaire.append(
                cell_to_variable(elem[0] + pos_i, elem[1] + pos_j, elem[2])
            )

    liste_clauses.append(liste_clauses_intermediaire)

    global liste_de_clauses
    liste_de_clauses = remove_duplicates(liste_de_clauses)

    # --------------- DEMANDE SAFE -----------------
    # Si on veut demander au solveur si la case est safe, on ajoute la liste de clauses qui dit que la case est unsafe (liste_clauses)
    if liste_clauses:
        liste_de_clauses += liste_clauses

    write_dimacs_file(clauses_to_dimacs(liste_de_clauses, nbVar_reel), "phase1.cnf")

    result_safe = exec_gophersat("phase1.cnf")

    # On enlève les clauses liées à la demande safe#
    liste_de_clauses = [
        element for element in liste_de_clauses if element not in liste_clauses
    ]

    # NE PAS DEMANDER UNSAFE SI ON A UNE REPONSE SAFE AVANT
    if result_safe[0]:
        # ---------------- DEMANDE UNSAFE -------------------
        # On veut tester si la case n'est pas safe pour sur, c'est-à-dire que la case est dans la vision des gardes
        # Si on veut demander au solveur si la case est unsafe, on ajoute la liste de clauses qui dit que la case est safe (non liste_clauses)
        liste_clauses_bis = []
        for elem in liste_clauses:
            for lit in elem:
                liste_clauses_bis.append([-lit])
        if liste_clauses_bis:
            liste_de_clauses += liste_clauses_bis
        write_dimacs_file(clauses_to_dimacs(liste_de_clauses, nbVar_reel), "phase1.cnf")

        result_unsafe = exec_gophersat("phase1.cnf")

        # On enlève les clauses liées à la demande unsafe
        liste_de_clauses = [
            element for element in liste_de_clauses if element not in liste_clauses_bis
        ]
        return not result_safe[0], not result_unsafe[0], 0, len(offset_vision)

    return not result_safe[0], False, 0, len(offset_vision)


def solver_phase1(status, map):
    global liste_de_clauses
    liste_de_clauses = initialize_regles(status, map)

    while any(value == 0 for value in map.values()):
        has_moved = False
        clauses_bruit = gestion_bruit(status)
        liste_de_clauses += clauses_bruit

        orientations = [HC.N, HC.S, HC.W, HC.E]
        orientation = status["orientation"]

        i = status["position"][0]
        j = status["position"][1]

        # On sauvegarde les orientations qui peuvent nous donner des infos nouvelles grâce à la vision
        # Ne gère pas les cas où la vision est stoppée par un objet/personne
        orientations_to_check = []
        blocking_items = [
            HC.CIVIL_N,
            HC.CIVIL_S,
            HC.CIVIL_E,
            HC.CIVIL_W,
            HC.WALL,
            HC.GUARD_N,
            HC.GUARD_S,
            HC.GUARD_E,
            HC.GUARD_W,
            HC.SUIT,
        ]

        for ori in orientations:
            cpt = 0
            if ori == HC.N:
                for x in range(1, 4):
                    if 0 <= j + x < m:
                        if map[(i, j + x)] == 0:
                            cpt += 1
                        if map[(i, j + x)] in blocking_items:
                            break
            elif ori == HC.E:
                for x in range(1, 4):
                    if 0 <= i + x < n:
                        if map[(i + x, j)] in blocking_items:
                            break
                        elif map[(i + x, j)] == 0:
                            cpt += 1
            elif ori == HC.W:
                for x in range(-1, -4, -1):
                    if 0 <= i + x < n:
                        if map[(i + x, j)] in blocking_items:
                            break
                        elif map[(i + x, j)] == 0:
                            cpt += 1
            elif ori == HC.S:
                for x in range(-1, -4, -1):
                    if 0 <= j + x < m:
                        if map[(i, j + x)] in blocking_items:
                            break
                        if map[(i, j + x)] == 0:
                            cpt += 1
            if cpt > 0:
                orientations_to_check.append(ori)

        # On conserve l'orientation qui permettra de savoir de là d'où il vient; ex: s'il se déplace vers le nord c'est qu'il vient du sud
        # Sauf au début mais ça n'a aucun impact de le garder donc aucun problème
        if orientation == HC.N:
            orientation_origine = HC.S
        elif orientation == HC.S:
            orientation_origine = HC.N
        elif orientation == HC.W:
            orientation_origine = HC.E
        else:
            orientation_origine = HC.W

        # On ne se tourne que vers les destinations intéressantes à observer
        for ori in orientations_to_check:
            if orientation == HC.N:
                if ori == HC.S:
                    status = hr.turn_clockwise()
                    status = hr.turn_clockwise()
                elif ori == HC.E:
                    status = hr.turn_clockwise()
                elif ori == HC.W:
                    status = hr.turn_anti_clockwise()

            elif orientation == HC.S:
                if ori == HC.N:
                    status = hr.turn_clockwise()
                    status = hr.turn_clockwise()
                elif ori == HC.E:
                    status = hr.turn_anti_clockwise()
                elif ori == HC.W:
                    status = hr.turn_clockwise()

            elif orientation == HC.E:
                if ori == HC.N:
                    status = hr.turn_anti_clockwise()
                elif ori == HC.W:
                    status = hr.turn_anti_clockwise()
                    status = hr.turn_anti_clockwise()
                elif ori == HC.S:
                    status = hr.turn_clockwise()

            elif orientation == HC.W:
                if ori == HC.N:
                    status = hr.turn_clockwise()
                elif ori == HC.E:
                    status = hr.turn_anti_clockwise()
                    status = hr.turn_anti_clockwise()
                elif ori == HC.S:
                    status = hr.turn_anti_clockwise()

            clauses_vision = gestion_vision(status)

            liste_de_clauses += clauses_vision

            for elem in clauses_vision:
                variable = variable_to_cell(elem[0])
                valeur = HC(variable[2] + 1)
                i = variable[0]
                j = variable[1]
                map[(i, j)] = valeur

            orientation = status["orientation"]

        i = status["position"][0]
        j = status["position"][1]
        afficher_grille(m, n, map, status)

        # Gestion déplacement

        # On récupère les directions possibles à partir de notre position
        dest = []
        for ori in orientations:
            ret = demande(i, j, ori, map)
            if ret[2] == 0:
                dest.append((ret[0], ret[1], ori, ret[3]))

        # S'il y a plusieurs destinations possibles, on enlève celle d'où on vient
        if len(dest) > 1:
            for destination in dest:
                if destination[2] == orientation_origine:
                    dest.remove(destination)

        # on met la meilleure en premier (au sens du nombre de cases à découvrir)
        # tri_selon_potentiel = dest.sort(key=lambda x: x[3], reverse=True)
        tri_selon_potentiel = sorted(dest, key=lambda x: x[3], reverse=True)
        tri_selon_unsafe = sorted(
            tri_selon_potentiel, key=lambda x: not x[1], reverse=True
        )
        #print(tri_selon_unsafe)
        # Si toutes les orientations de tri_selon_unsafe ont un potentiel de vision =
        # Et qu'elles ne se distinguent pas par le caractère "safe" de la case
        # Alors on lance une demande de safe sur la case située 1 case plus loin
        nb_orientations = len(tri_selon_unsafe)
        second_tab = []
        indecision = False
        # Cas où y'aurait une indécision si on enlevait l'orientation qui est sure d'être pas safe (car avant on rentrait pas dans la boucle d'indécision)
        at_least_one_not_unsafe = False
        for orientations in tri_selon_unsafe:
            if not orientations[1]:
                at_least_one_not_unsafe = True

        if (
            nb_orientations > 1 and at_least_one_not_unsafe
        ):  # si on est pas dans un cas ou on est contraints
            for orientations in tri_selon_unsafe.copy():
                if orientations[
                    1
                ]:  # si l'orientaaiton est forcément unsafe on la dégage
                    tri_selon_unsafe.remove(orientations)
        #print(tri_selon_unsafe)
        nb_orientations = len(tri_selon_unsafe)
        if (
            nb_orientations == 2
            and tri_selon_unsafe[0][3] == tri_selon_unsafe[1][3]
            and tri_selon_unsafe[0][0]
            and tri_selon_unsafe[1][0]
        ) or (
            nb_orientations == 2
            and tri_selon_unsafe[0][3] == tri_selon_unsafe[1][3] == 0
        ):
            indecision = True
            for iter in range(nb_orientations):
                if tri_selon_unsafe[iter][2] == HC.N:
                    #print(demande(i, j + 1, HC.N, map))
                    potentiel = demande(i, j + 1, HC.N, map)[3]
                    second_tab.append((HC.N, potentiel))
                elif tri_selon_unsafe[iter][2] == HC.S:
                    #print(demande(i, j - 1, HC.S, map))
                    potentiel = demande(i, j - 1, HC.S, map)[3]
                    second_tab.append((HC.S, potentiel))
                elif tri_selon_unsafe[iter][2] == HC.W:
                    #print(demande(i - 1, j, HC.W, map))
                    potentiel = demande(i - 1, j, HC.W, map)[3]
                    second_tab.append((HC.W, potentiel))
                else:
                    #print(demande(i + 1, j, HC.E, map))
                    potentiel = demande(i + 1, j, HC.E, map)[3]
                    second_tab.append((HC.E, potentiel))
        elif (
            nb_orientations == 3
            and tri_selon_unsafe[0][3] == tri_selon_unsafe[1][3]
            and tri_selon_unsafe[1][3] == tri_selon_unsafe[2][3]
            and tri_selon_unsafe[0][0]
            and tri_selon_unsafe[1][0]
            and tri_selon_unsafe[2][0]
        ) or (
            nb_orientations == 3
            and tri_selon_unsafe[0][3]
            == tri_selon_unsafe[1][3]
            == tri_selon_unsafe[2][3]
            == 0
        ):
            indecision = True
            for iter in range(nb_orientations):
                if tri_selon_unsafe[iter][2] == HC.N:
                    potentiel = demande(i, j + 1, HC.N, map)[3]
                    second_tab.append((HC.N, potentiel))
                elif tri_selon_unsafe[iter][2] == HC.S:
                    potentiel = demande(i, j - 1, HC.S, map)[3]
                    second_tab.append((HC.S, potentiel))
                elif tri_selon_unsafe[iter][2] == HC.W:
                    potentiel = demande(i - 1, j, HC.W, map)[3]
                    second_tab.append((HC.W, potentiel))
                else:
                    potentiel = demande(i + 1, j, HC.E, map)[3]
                    second_tab.append((HC.E, potentiel))
        elif (
            nb_orientations == 4
            and tri_selon_unsafe[0][3] == tri_selon_unsafe[1][3]
            and tri_selon_unsafe[1][3] == tri_selon_unsafe[2][3]
            and tri_selon_unsafe[2][3] == tri_selon_unsafe[3][3]
            and tri_selon_unsafe[0][0]
            and tri_selon_unsafe[1][0]
            and tri_selon_unsafe[2][0]
            and tri_selon_unsafe[3][0]
        ) or (
            nb_orientations == 4
            and tri_selon_unsafe[0][3]
            == tri_selon_unsafe[1][3]
            == tri_selon_unsafe[2][3]
            == tri_selon_unsafe[3][3]
            == 0
        ):
            indecision = True
            for iter in range(nb_orientations):
                if tri_selon_unsafe[iter][2] == HC.N:
                    potentiel = demande(i, j + 1, HC.N, map)[3]
                    second_tab.append((HC.N, potentiel))
                elif tri_selon_unsafe[iter][2] == HC.S:
                    potentiel = demande(i, j - 1, HC.S, map)[3]
                    second_tab.append((HC.S, potentiel))
                elif tri_selon_unsafe[iter][2] == HC.W:
                    potentiel = demande(i - 1, j, HC.W, map)[3]
                    second_tab.append((HC.W, potentiel))
                else:
                    potentiel = demande(i + 1, j, HC.E, map)[3]
                    second_tab.append((HC.E, potentiel))

        if indecision:
            # On trie second_tab selon le potentiel
            second_tab = sorted(second_tab, key=lambda x: x[1], reverse=True)
            #print(second_tab)
            orientation_gagnante = second_tab[0][0]

            copy = tri_selon_unsafe[:]
            for elem in copy:
                if elem[2] == orientation_gagnante:
                    tri_selon_unsafe.remove(elem)
                    tri_selon_unsafe.insert(0, elem)
                    break  # On a trouvé l'orientation gagnante, on peut sortir de la boucle

        for couple_safe_ori in tri_selon_unsafe:
            # Si la destination est safe, on se tourne dans la bonne direction et on bouge. Dans le cas où il y a une
            # destination safe et une possible mais pas forcément safe (au moins), on peut favoriser celle qui n'est pas forcément
            # safe si on est sur de découvrir 0 case en allant sur la safe (en gros selon la situation, on privilégie celle qui
            # nous donnera le plus d'infos utiles

            # Si la destination est safe et qu'elle a un potentiel au moins supérieur à 1 ou alors elle est unique, alors on la privilégie.
            if couple_safe_ori[0] and (
                couple_safe_ori[3] > 1 or len(tri_selon_unsafe) <= 1
            ):
                if (
                    orientation == couple_safe_ori[2]
                ):  # Si on est déjà dans la bonne direction
                    status = hr.move()
                    has_moved = True
                else:  # Sinon on se tourne dans la bonne direction
                    if orientation == HC.N:
                        if couple_safe_ori[2] == HC.E:
                            status = hr.turn_clockwise()
                        elif couple_safe_ori[2] == HC.W:
                            status = hr.turn_anti_clockwise()
                        else:
                            status = hr.turn_clockwise()
                            status = hr.turn_clockwise()
                    elif orientation == HC.S:
                        if couple_safe_ori[2] == HC.E:
                            status = hr.turn_anti_clockwise()
                        elif couple_safe_ori[2] == HC.W:
                            status = hr.turn_clockwise()
                        else:
                            status = hr.turn_clockwise()
                            status = hr.turn_clockwise()
                    elif orientation == HC.E:
                        if couple_safe_ori[2] == HC.N:
                            status = hr.turn_anti_clockwise()
                        elif couple_safe_ori[2] == HC.S:
                            status = hr.turn_clockwise()
                        else:
                            status = hr.turn_clockwise()
                            status = hr.turn_clockwise()
                    elif orientation == HC.W:
                        if couple_safe_ori[2] == HC.N:
                            status = hr.turn_clockwise()
                        elif couple_safe_ori[2] == HC.S:
                            status = hr.turn_anti_clockwise()
                        else:
                            status = hr.turn_clockwise()
                            status = hr.turn_clockwise()
                    status = hr.move()
                    has_moved = True
        #print(tri_selon_unsafe)
        # Sinon, on prend la premiere orientation (celle qui a été ajoutée au dessus)
        if not has_moved:
            # on prend la première destination possible
            best_ori = tri_selon_unsafe[0][2]
            if orientation == best_ori:
                status = hr.move()
            else:
                if orientation == HC.N:
                    if best_ori == HC.E:
                        status = hr.turn_clockwise()
                    elif best_ori == HC.W:
                        status = hr.turn_anti_clockwise()
                    else:
                        status = hr.turn_clockwise()
                        status = hr.turn_clockwise()
                elif orientation == HC.S:
                    if best_ori == HC.E:
                        status = hr.turn_anti_clockwise()
                    elif best_ori == HC.W:
                        status = hr.turn_clockwise()
                    else:
                        status = hr.turn_clockwise()
                        status = hr.turn_clockwise()
                elif orientation == HC.E:
                    if best_ori == HC.N:
                        status = hr.turn_anti_clockwise()
                    elif best_ori == HC.S:
                        status = hr.turn_clockwise()
                    else:
                        status = hr.turn_clockwise()
                        status = hr.turn_clockwise()
                elif orientation == HC.W:
                    if best_ori == HC.N:
                        status = hr.turn_clockwise()
                    elif best_ori == HC.S:
                        status = hr.turn_anti_clockwise()
                    else:
                        status = hr.turn_clockwise()
                        status = hr.turn_clockwise()
                status = hr.move()
    #print(f"Pénalités obtenues phase 1: {status['penalties']}")
    print("\n\n")


def afficher_grille(nb_lignes, nb_colonnes, dictionnaire, status):
    pos = status["position"]
    ori = status["orientation"]
    ligne_delim = "+" + "----+" * nb_colonnes  # Ligne de délimitation horizontale

    for ligne in range(nb_lignes - 1, -1, -1):
        print(
            ligne_delim
        )  # Afficher la ligne de délimitation horizontale avant chaque ligne de cases
        for colonne in range(nb_colonnes):
            case = dictionnaire.get((colonne, ligne))
            if case is None:
                print("|   ", end="")  # Afficher une case vide
            elif pos[0] == colonne and pos[1] == ligne:
                if ori.name == "N":
                    print("| ★↑ ", end="")
                elif ori.name == "E":
                    print("| ★→ ", end="")
                elif ori.name == "S":
                    print("| ★↓ ", end="")
                elif ori.name == "W":
                    print("| ★← ", end="")
            elif case == 0:
                print("| 0  ", end="")  # Afficher une case contenant un zéro
            else:
                if case.name.endswith("_N"):
                    initial = case.name[0] + "↑"
                elif case.name.endswith("_E"):
                    initial = case.name[0] + "→"
                elif case.name.endswith("_S"):
                    initial = case.name[0] + "↓"
                elif case.name.endswith("_W"):
                    initial = case.name[0] + "←"
                else:
                    initial = case.name[0] + " "
                print(
                    f"| {initial} ", end=""
                )  # Afficher une case avec une autre valeur
        print("|")  # Fermer la ligne avec un délimiteur vertical final
    print(
        ligne_delim
    )  # Afficher la ligne de délimitation horizontale en bas de la grille


def set_empty_map() -> Dict:
    # Si on fait une map comme dans l'arbitre
    map = {(i, j): 0 for i in range(n) for j in range(m)}
    return map


# ------------------- FIN GESTION PHASE 1 -------------------

# ------------------- DEBUT GESTION PHASE 2 -------------------

State = Dict


def clone(s: State) -> State:
    s2 = {}
    for k in s:
        s2[k] = s[k][:]
    return s2


def is_final(status: Dict, true_map: Dict, s: State) -> bool:
    our_i, our_j = status["position"]
    for position, variable in true_map.items():
        if variable == HC.TARGET:
            target_i, target_j = position
    return (
        (our_i == 0 and our_j == 0)
        and ((target_i, target_j) in s[HC.EMPTY])
        and (
            (0, 0) in s[HC.N]
            or (0, 0) in s[HC.S]
            or (0, 0) in s[HC.E]
            or (0, 0) in s[HC.W]
        )
    )


def initial_state(status: Dict, true_map: Dict) -> Dict:
    dictionnary = {value: [] for value in HC}

    for position, value in true_map.items():
        dictionnary[value].append(position)

    orientation = status["orientation"]
    dictionnary[orientation].append((0, 0))

    # Ajouter une clé "vision_guard_civil" qui représente les cases dans la portée d'un garde ou d'un civil
    dictionnary["vision_guard_civil"] = []

    # Ajouter une clé "vision_guard" qui symbolise la vision des gardes uniquement et donc des cases qui nous feront
    # prendre des pénalités
    dictionnary["vision_guard"] = []
    dictionnary["a_neutraliser"] = []
    i_cible, j_cible = dictionnary[HC.TARGET][0]
    for key, value in dictionnary.items():
        if key == HC.GUARD_N:
            for pos in value:
                for j in range(1, 3):
                    # on n'ajoute pas dans la liste des cases visibles par les gardes les cases qui sont masquées par des civils, not_masquage_civil est vrai si la case n'est pas masquée par un civil
                    not_masquage_civil = (
                        not (pos[0], pos[1] + j) in dictionnary[HC.CIVIL_N]
                        and not (pos[0], pos[1] + j) in dictionnary[HC.CIVIL_S]
                        and not (pos[0], pos[1] + j) in dictionnary[HC.CIVIL_E]
                        and not (pos[0], pos[1] + j) in dictionnary[HC.CIVIL_W]
                    )
                    if not not_masquage_civil:
                        break
                    if (
                        0 <= pos[1] + j < m
                        and not (pos[0], pos[1] + j) in dictionnary[HC.WALL]
                        and not_masquage_civil
                    ):
                        dictionnary["vision_guard"].append((pos[0], pos[1] + j))
                        dictionnary["vision_guard_civil"].append((pos[0], pos[1] + j))
                        # Si le garde ou le civil voit la cible, on l'ajoute à la liste des cases à neutraliser
                        if pos[0] == i_cible and pos[1] + j == j_cible:
                            dictionnary["a_neutraliser"].append((pos[0], pos[1]))
        elif key == HC.CIVIL_N:
            for pos in value:
                for j in range(1, 2):
                    not_masquage_civil = (
                        not (pos[0], pos[1] + j) in dictionnary[HC.CIVIL_N]
                        and not (pos[0], pos[1] + j) in dictionnary[HC.CIVIL_S]
                        and not (pos[0], pos[1] + j) in dictionnary[HC.CIVIL_E]
                        and not (pos[0], pos[1] + j) in dictionnary[HC.CIVIL_W]
                    )
                    if not not_masquage_civil:
                        break
                    if (
                        0 <= pos[1] + j < m
                        and not (pos[0], pos[1] + j) in dictionnary[HC.WALL]
                        and not_masquage_civil
                    ):
                        dictionnary["vision_guard_civil"].append((pos[0], pos[1] + j))
                        # Si le garde ou le civil voit la cible, on l'ajoute à la liste des cases à neutraliser
                        if pos[0] == i_cible and pos[1] + j == j_cible:
                            dictionnary["a_neutraliser"].append((pos[0], pos[1]))
        elif key == HC.GUARD_S:
            for pos in value:
                for j in range(-1, -3, -1):
                    not_masquage_civil = (
                        not (pos[0], pos[1] + j) in dictionnary[HC.CIVIL_N]
                        and not (pos[0], pos[1] + j) in dictionnary[HC.CIVIL_S]
                        and not (pos[0], pos[1] + j) in dictionnary[HC.CIVIL_E]
                        and not (pos[0], pos[1] + j) in dictionnary[HC.CIVIL_W]
                    )
                    if not not_masquage_civil:
                        break

                    if (
                        0 <= pos[1] + j < m
                        and not (pos[0], pos[1] + j) in dictionnary[HC.WALL]
                        and not_masquage_civil
                    ):
                        dictionnary["vision_guard"].append((pos[0], pos[1] + j))
                        dictionnary["vision_guard_civil"].append((pos[0], pos[1] + j))
                        # Si le garde ou le civil voit la cible, on l'ajoute à la liste des cases à neutraliser
                        if pos[0] == i_cible and pos[1] + j == j_cible:
                            dictionnary["a_neutraliser"].append((pos[0], pos[1]))
        elif key == HC.CIVIL_S:
            for pos in value:
                for j in range(-1, 0, 1):
                    not_masquage_civil = (
                        not (pos[0], pos[1] + j) in dictionnary[HC.CIVIL_N]
                        and not (pos[0], pos[1] + j) in dictionnary[HC.CIVIL_S]
                        and not (pos[0], pos[1] + j) in dictionnary[HC.CIVIL_E]
                        and not (pos[0], pos[1] + j) in dictionnary[HC.CIVIL_W]
                    )
                    if not not_masquage_civil:
                        break
                    if (
                        0 <= pos[1] + j < m
                        and not (pos[0], pos[1] + j) in dictionnary[HC.WALL]
                        and not_masquage_civil
                    ):
                        dictionnary["vision_guard_civil"].append((pos[0], pos[1] + j))
                        # Si le garde ou le civil voit la cible, on l'ajoute à la liste des cases à neutraliser
                        if pos[0] == i_cible and pos[1] + j == j_cible:
                            dictionnary["a_neutraliser"].append((pos[0], pos[1]))
        elif key == HC.GUARD_E:
            for pos in value:
                for i in range(1, 3):
                    not_masquage_civil = (
                        not (pos[0] + i, pos[1]) in dictionnary[HC.CIVIL_N]
                        and not (pos[0] + i, pos[1]) in dictionnary[HC.CIVIL_S]
                        and not (pos[0] + i, pos[1]) in dictionnary[HC.CIVIL_E]
                        and not (pos[0] + i, pos[1]) in dictionnary[HC.CIVIL_W]
                    )
                    if not not_masquage_civil:
                        break
                    if (
                        0 <= pos[0] + i < n
                        and not (pos[0] + i, pos[1]) in dictionnary[HC.WALL]
                        and not_masquage_civil
                    ):
                        dictionnary["vision_guard"].append((pos[0] + i, pos[1]))
                        dictionnary["vision_guard_civil"].append((pos[0] + i, pos[1]))
                        # Si le garde ou le civil voit la cible, on l'ajoute à la liste des cases à neutraliser
                        if pos[0] + i == i_cible and pos[1] == j_cible:
                            dictionnary["a_neutraliser"].append((pos[0], pos[1]))
        elif key == HC.CIVIL_E:
            for pos in value:
                for i in range(1, 2):
                    not_masquage_civil = (
                        not (pos[0] + i, pos[1]) in dictionnary[HC.CIVIL_N]
                        and not (pos[0] + i, pos[1]) in dictionnary[HC.CIVIL_S]
                        and not (pos[0] + i, pos[1]) in dictionnary[HC.CIVIL_E]
                        and not (pos[0] + i, pos[1]) in dictionnary[HC.CIVIL_W]
                    )
                    if not not_masquage_civil:
                        break
                    if (
                        0 <= pos[0] + i < n
                        and not (pos[0] + i, pos[1]) in dictionnary[HC.WALL]
                        and not_masquage_civil
                    ):
                        dictionnary["vision_guard_civil"].append((pos[0] + i, pos[1]))
                        # Si le garde ou le civil voit la cible, on l'ajoute à la liste des cases à neutraliser
                        if pos[0] + i == i_cible and pos[1] == j_cible:
                            dictionnary["a_neutraliser"].append((pos[0], pos[1]))
        elif key == HC.GUARD_W:
            for pos in value:
                for i in range(-1, -3, -1):
                    not_masquage_civil = (
                        not (pos[0] + i, pos[1]) in dictionnary[HC.CIVIL_N]
                        and not (pos[0] + i, pos[1]) in dictionnary[HC.CIVIL_S]
                        and not (pos[0] + i, pos[1]) in dictionnary[HC.CIVIL_E]
                        and not (pos[0] + i, pos[1]) in dictionnary[HC.CIVIL_W]
                    )
                    if not not_masquage_civil:
                        break
                    if (
                        0 <= pos[0] + i < n
                        and not (pos[0] + i, pos[1]) in dictionnary[HC.WALL]
                        and not_masquage_civil
                    ):
                        dictionnary["vision_guard"].append((pos[0] + i, pos[1]))
                        dictionnary["vision_guard_civil"].append((pos[0] + i, pos[1]))
                        # Si le garde ou le civil voit la cible, on l'ajoute à la liste des cases à neutraliser
                        if pos[0] + i == i_cible and pos[1] == j_cible:
                            dictionnary["a_neutraliser"].append((pos[0], pos[1]))
        elif key == HC.CIVIL_W:
            for pos in value:
                for i in range(-1, 0, 1):
                    not_masquage_civil = (
                        not (pos[0] + i, pos[1]) in dictionnary[HC.CIVIL_N]
                        and not (pos[0] + i, pos[1]) in dictionnary[HC.CIVIL_S]
                        and not (pos[0] + i, pos[1]) in dictionnary[HC.CIVIL_E]
                        and not (pos[0] + i, pos[1]) in dictionnary[HC.CIVIL_W]
                    )
                    if not not_masquage_civil:
                        break
                    if (
                        0 <= pos[0] + i < n
                        and not (pos[0] + i, pos[1]) in dictionnary[HC.WALL]
                        and not_masquage_civil
                    ):
                        dictionnary["vision_guard_civil"].append((pos[0] + i, pos[1]))
                        # Si le garde ou le civil voit la cible, on l'ajoute à la liste des cases à neutraliser
                        if pos[0] + i == i_cible and pos[1] == j_cible:
                            dictionnary["a_neutraliser"].append((pos[0], pos[1]))
    return dictionnary


def turn_N(s: State, status: Dict) -> Tuple[Dict, State]:
    # precond
    precond = len(s[HC.N]) == 0

    if not precond:
        return status, s

    # effects
    i, j = status["position"]
    current_orientation = status["orientation"]

    if current_orientation == HC.S:
        status = hr.turn_clockwise()
        status = hr.turn_clockwise()
    elif current_orientation == HC.E:
        status = hr.turn_anti_clockwise()
    elif current_orientation == HC.W:
        status = hr.turn_clockwise()

    s2 = clone(s)
    s2[current_orientation].remove((i, j))
    s2[HC.N].append((i, j))
    return status, s2


def turn_S(s: State, status: Dict) -> Tuple[Dict, State]:
    # precond
    precond = len(s[HC.S]) == 0

    if not precond:
        return status, s

    # effects
    i, j = status["position"]
    current_orientation = status["orientation"]

    if current_orientation == HC.N:
        status = hr.turn_clockwise()
        status = hr.turn_clockwise()
    elif current_orientation == HC.W:
        status = hr.turn_anti_clockwise()
    elif current_orientation == HC.E:
        status = hr.turn_clockwise()

    s2 = clone(s)
    s2[current_orientation].remove((i, j))
    s2[HC.S].append((i, j))
    return status, s2


def turn_E(s: State, status: Dict) -> Tuple[Dict, State]:
    # precond
    precond = len(s[HC.E]) == 0

    if not precond:
        return status, s

    # effects
    i, j = status["position"]
    current_orientation = status["orientation"]
    if current_orientation == HC.W:
        status = hr.turn_clockwise()
        status = hr.turn_clockwise()
    elif current_orientation == HC.S:
        status = hr.turn_anti_clockwise()
    elif current_orientation == HC.N:
        status = hr.turn_clockwise()

    s2 = clone(s)
    s2[current_orientation].remove((i, j))
    s2[HC.E].append((i, j))
    return status, s2


def turn_W(s: State, status: Dict) -> Tuple[Dict, State]:
    # precond
    precond = len(s[HC.W]) == 0

    if not precond:
        return status, s

    # effects
    i, j = status["position"]
    current_orientation = status["orientation"]

    if current_orientation == HC.E:
        status = hr.turn_clockwise()
        status = hr.turn_clockwise()
    elif current_orientation == HC.N:
        status = hr.turn_anti_clockwise()
    elif current_orientation == HC.S:
        status = hr.turn_clockwise()

    s2 = clone(s)
    s2[current_orientation].remove((i, j))
    s2[HC.W].append((i, j))
    return status, s2


def move_N(s: State, status: Dict) -> Tuple[Dict, State]:
    i, j = status["position"]
    j2 = j + 1

    precond = (
        len(s[HC.N]) == 1
        and not ((i, j2) in s[HC.GUARD_N])
        and not ((i, j2) in s[HC.GUARD_S])
        and not ((i, j2) in s[HC.GUARD_E])
        and not ((i, j2) in s[HC.GUARD_W])
        and not ((i, j2) in s[HC.WALL])
        and not (j2 < 0)
    )
    if not precond:
        return status, s

    s2 = clone(s)
    s2[HC.N][0] = (i, j2)
    status = hr.move()
    return status, s2


def move_S(s: State, status: Dict) -> Tuple[Dict, State]:
    i, j = status["position"]
    j2 = j - 1
    precond = (
        len(s[HC.S]) == 1
        and not ((i, j2) in s[HC.GUARD_N])
        and not ((i, j2) in s[HC.GUARD_S])
        and not ((i, j2) in s[HC.GUARD_E])
        and not ((i, j2) in s[HC.GUARD_W])
        and not ((i, j2) in s[HC.WALL])
        and not (j2 < 0)
    )
    if not precond:
        return status, s

    s2 = clone(s)
    s2[HC.S][0] = (i, j2)
    status = hr.move()
    return status, s2


def move_E(s: State, status: Dict) -> Tuple[Dict, State]:
    i, j = status["position"]
    i2 = i + 1
    # print(s[HC.GUARD_N])
    # print(s[HC.WALL])
    precond = (
        len(s[HC.E]) == 1
        and not ((i2, j) in s[HC.GUARD_N])
        and not ((i2, j) in s[HC.GUARD_S])
        and not ((i2, j) in s[HC.GUARD_E])
        and not ((i2, j) in s[HC.GUARD_W])
        and not ((i2, j) in s[HC.WALL])
        and not (i2 >= n)
    )
    if not precond:
        return status, s

    s2 = clone(s)
    s2[HC.E][0] = (i2, j)
    status = hr.move()
    return status, s2


def move_W(s: State, status: Dict) -> Tuple[Dict, State]:
    i, j = status["position"]
    i2 = i - 1
    precond = (
        len(s[HC.W]) == 1
        and not ((i2, j) in s[HC.GUARD_N])
        and not ((i2, j) in s[HC.GUARD_S])
        and not ((i2, j) in s[HC.GUARD_E])
        and not ((i2, j) in s[HC.GUARD_W])
        and not ((i2, j) in s[HC.WALL])
        and not (i2 < 0)
    )
    if not precond:
        return status, s
    s2 = clone(s)
    s2[HC.W][0] = (i2, j)
    #print("s2[HC.W]: ", s2[HC.W])
    status = hr.move()
    return status, s2


def take_weapon(s: State, status: Dict) -> Tuple[Dict, State]:
    # precond
    i, j = status["position"]
    orientation = status["orientation"]
    precond = (
        (i, j) in s[orientation]
        and (i, j) in s[HC.PIANO_WIRE]
        and not status["has_weapon"]
    )
    if not precond:
        return status, s

    # effects
    status = hr.take_weapon()
    s2 = clone(s)
    s2[HC.PIANO_WIRE].remove((i, j))
    s2[HC.EMPTY].append((i, j))
    return status, s2


def take_suit(s: State, status: Dict) -> Tuple[Dict, State]:
    # precond
    current_orientation = status["orientation"]
    i, j = status["position"]
    precond = (
        (i, j) in s[current_orientation]
        and (i, j) in s[HC.SUIT]
        and not status["has_suit"]
        and not status["is_suit_on"]
    )

    if not precond:
        return status, s

    # effects
    status = hr.take_suit()
    s2 = clone(s)
    s2[HC.SUIT].remove((i, j))
    s2[HC.EMPTY].append((i, j))
    return status, s2


def put_on_suit(s: State, status: Dict) -> Tuple[Dict, State]:
    # precond
    precond = status["has_suit"] and not status["is_suit_on"]
    if not precond:
        return status, s

    # effects
    status = hr.put_on_suit()
    return status, s


def kill_target(s: State, status: Dict) -> Tuple[Dict, State]:
    i, j = status["position"]
    orientation = status["orientation"]
    precond = (
        (i, j) in s[orientation] and status["has_weapon"] and (i, j) in s[HC.TARGET]
    )
    if not precond:
        return status, s

    # effects
    status = hr.kill_target()
    s2 = clone(s)
    s2[HC.TARGET].remove((i, j))
    s2[HC.EMPTY].append((i, j))
    return status, s2


def neutralize_guard(s: State, status: Dict) -> Tuple[Dict, State]:
    i, j = status["position"]
    orientation = status["orientation"]
    j_not_safe_2 = 0
    j_not_safe_1 = 0
    j_not_safe = 0
    i2 = 0
    j2 = 0
    i_not_safe_1 = 0
    i_not_safe_2 = 0
    # stocker l'orientation du garde qui regarde dans l'opposé de notre direction (danger) : si orientation = HC.N alors on stocke l'orientation HC.GUARD_S
    if orientation == HC.N:
        guard_orientation = HC.GUARD_S
        i2 = i
        j2 = j + 1
    elif orientation == HC.S:
        guard_orientation = HC.GUARD_N
        i2 = i
        j2 = j - 1

    elif orientation == HC.E:
        guard_orientation = HC.GUARD_W
        i2 = i + 1
        j2 = j

    elif orientation == HC.W:
        guard_orientation = HC.GUARD_E
        i2 = i - 1
        j2 = j

    if (i2, j2) in s[HC.GUARD_N]:
        i_not_safe = i2
        j_not_safe_1 = j2 + 1
        j_not_safe_2 = j2 + 2
    elif (i2, j2) in s[HC.GUARD_S]:
        i_not_safe = i2
        j_not_safe_1 = j2 - 1
        j_not_safe_2 = j2 - 2
    elif (i2, j2) in s[HC.GUARD_E]:
        i_not_safe_1 = i2 - 1
        i_not_safe_2 = i2 - 2
        j_not_safe = j2
    elif (i2, j2) in s[HC.GUARD_W]:
        i_not_safe_1 = i2 + 1
        i_not_safe_2 = i2 + 2
        j_not_safe = j2

    precond = (i, j) in s[orientation] and (i2, j2) not in s[guard_orientation]
    if not precond:
        return status, s
    # on stocke tous les guard sauf guard_orientation
    guards = [HC.GUARD_N, HC.GUARD_S, HC.GUARD_E, HC.GUARD_W]
    guards.remove(guard_orientation)
    status = hr.neutralize_guard()
    s2 = clone(s)
    for guard in guards:
        if (i2, j2) in s[guard]:
            s2[guard].remove((i2, j2))
            if guard == HC.GUARD_N:
                s2["vision_guard_civil"].remove((i2, j_not_safe_1))
                s2["vision_guard_civil"].remove((i2, j_not_safe_2))
            elif guard == HC.GUARD_S:
                s2["vision_guard_civil"].remove((i2, j_not_safe_1))
                s2["vision_guard_civil"].remove((i2, j_not_safe_2))
            elif guard == HC.GUARD_W:
                s2["vision_guard_civil"].remove((i_not_safe_1, j_not_safe))
                s2["vision_guard_civil"].remove((i_not_safe_2, j_not_safe))
            elif guard == HC.GUARD_E:
                s2["vision_guard_civil"].remove((i_not_safe_1, j_not_safe))
                s2["vision_guard_civil"].remove((i_not_safe_2, j_not_safe))
    s2[HC.EMPTY].append((i2, j2))
    return status, s2


def neutralize_civil(s: State, status: Dict) -> Tuple[Dict, State]:
    i, j = status["position"]
    orientation = status["orientation"]
    # stocker l'orientation du civil qui regarde dans l'opposé de notre direction (danger) : si orientation = HC.N alors on stocke l'orientation HC.CIVIL_S
    if orientation == HC.N:
        civil_orientation = HC.CIVIL_S
        i2 = i
        j2 = j + 1
    elif orientation == HC.S:
        civil_orientation = HC.CIVIL_N
        i2 = i
        j2 = j - 1
    elif orientation == HC.E:
        civil_orientation = HC.CIVIL_W
        i2 = i + 1
        j2 = j
    elif orientation == HC.W:
        civil_orientation = HC.CIVIL_E
        i2 = i - 1
        j2 = j

    precond = (i, j) in s[orientation] and (i2, j2) not in s[civil_orientation]
    if not precond:
        return status, s

    # on stocke tous les civil sauf civil_orientation
    civils = [HC.CIVIL_N, HC.CIVIL_S, HC.CIVIL_E, HC.CIVIL_W]
    civils.remove(civil_orientation)
    status = hr.neutralize_civil()
    print("civil neutralisé")
    s2 = clone(s)
    for civil in civils:
        if (i2, j2) in s[civil]:
            s2[civil].remove((i2, j2))
    s2[HC.EMPTY].append((i2, j2))
    return status, s2


Action_id = str
Action = Callable[[State, Dict], Optional[State]]

action_id_to_action: Dict[Action_id, Action] = {
    "move_N": move_N,
    "move_S": move_S,
    "move_E": move_E,
    "move_W": move_W,
    "turn_N": turn_N,
    "turn_S": turn_S,
    "turn_E": turn_E,
    "turn_W": turn_W,
    "put_on_suit": put_on_suit,
    "neutralize_civil": neutralize_civil,
    "neutralize_guard": neutralize_guard,
    "take_suit": take_suit,
    "take_weapon": take_weapon,
    "kill_target": kill_target,
}
Plan = List[Action_id]


def distance_manhattan(pos_1: Tuple[int, int], pos_2: Tuple[int, int]) -> int:
    return abs(pos_1[0] - pos_2[0]) + abs(pos_1[1] - pos_2[1])


class Node:
    def __init__(self, i, j, cout, heuristique, parent=None):
        self.i = i
        self.j = j
        self.cout = cout
        self.heuristique = heuristique
        self.parent = parent

    def __lt__(self, other):
        return compareParHeuristique(self, other)

    def __eq__(self, other):
        return isinstance(other, Node) and self.i == other.i and self.j == other.j


# Implémentation de l'algorithme A*
def compareParHeuristique(n1: Node, n2: Node):
    if n1.heuristique < n2.heuristique:
        return True
    elif n1.heuristique == n2.heuristique:
        return 0
    else:
        return False


def reconstruireChemin(noeud):
    chemin = []
    current = noeud
    while current is not None:
        chemin.append((current.i, current.j))
        current = current.parent
    return chemin[::-1]


def a_star(s0: State, status: Dict, objectif: Node, depart: Node):
    # on déclare une file closedLists
    closedLists = []
    # on déclare une file de priorité openlist
    openList = []
    heapq.heapify(openList)
    heapq.heappush(openList, depart)
    while len(openList) != 0:
        # on dépile le noeud courant
        u = heapq.heappop(openList)
        # on ajoute le noeud courant dans la closedLists
        closedLists.append(u)
        # si le noeud courant est l'objectif, on retourne le chemin
        if u.i == objectif.i and u.j == objectif.j:
            chemin = reconstruireChemin(u)
            #print("Chemin trouvé :", chemin)
            return chemin
        # sinon on ajoute les noeuds voisins dans l'openList
        else:
            # on déclare une liste de noeuds voisins
            voisins = []
            cant_go = [HC.WALL, HC.GUARD_S, HC.GUARD_N, HC.GUARD_E, HC.GUARD_W]
            # on ajoute les noeuds voisins dans la liste
            if u.i + 1 < n:
                is_valid = True
                for variable in cant_go:
                    if (u.i + 1, u.j) in s0[variable]:
                        is_valid = False
                        break
                if is_valid:
                    voisins.append(
                        Node(
                            u.i + 1,
                            u.j,
                            u.cout + 1,
                            u.cout
                            + 1
                            + distance_manhattan(
                                (u.i + 1, u.j), (objectif.i, objectif.j)
                            ),
                            u,
                        )
                    )
            if u.i - 1 >= 0:
                is_valid = True
                for variable in cant_go:
                    if (u.i - 1, u.j) in s0[variable]:
                        is_valid = False
                        break
                if is_valid:
                    voisins.append(
                        Node(
                            u.i - 1,
                            u.j,
                            u.cout + 1,
                            u.cout
                            + 1
                            + distance_manhattan(
                                (u.i - 1, u.j), (objectif.i, objectif.j)
                            ),
                            u,
                        )
                    )
            if u.j + 1 < m:
                is_valid = True
                for variable in cant_go:
                    if (u.i, u.j + 1) in s0[variable]:
                        is_valid = False
                        break
                if is_valid:
                    voisins.append(
                        Node(
                            u.i,
                            u.j + 1,
                            u.cout + 1,
                            u.cout
                            + 1
                            + distance_manhattan(
                                (u.i, u.j + 1), (objectif.i, objectif.j)
                            ),
                            u,
                        )
                    )
            if u.j - 1 >= 0:
                is_valid = True
                for variable in cant_go:
                    if (u.i, u.j - 1) in s0[variable]:
                        is_valid = False
                        break
                if is_valid:
                    voisins.append(
                        Node(
                            u.i,
                            u.j - 1,
                            u.cout + 1,
                            u.cout
                            + 1
                            + distance_manhattan(
                                (u.i, u.j - 1), (objectif.i, objectif.j)
                            ),
                            u,
                        )
                    )

            # Vérifier si les voisins ne sont pas des cases dans la vision des gardes
            # Auquel cas on doit éviter. Si c'est la seule solution alors on laisse
            """
            voisins_unsafe = []
            for voisin in voisins:
                if (voisin.i, voisin.j) in s0["vision_guard"]:
                    voisins_unsafe.append(voisin)

            if len(voisins_unsafe) == 1 and len(voisins) == 2:
                if u.parent in voisins:
                    voisins.remove(u.parent)
            else:
                for voisin in voisins_unsafe:
                    voisins.remove(voisin)
            """
            # pour chaque noeud voisin
            for voisin in voisins:
                # si le noeud voisin n'est pas dans la closedLists
                if not any(noeud == voisin for noeud in closedLists):
                    voisin.parent = (
                        u  # Définir le parent du voisin comme le nœud actuel
                    )
                    # on ajoute le noeud voisin dans l'openList
                    heapq.heappush(openList, voisin)


def establish_route(
    s: State, status: Dict, objectif: Node, depart: Node
) -> Optional[List[Tuple[int, int]]]:
    return a_star(s, status, objectif, depart)


def convert_route_to_plan(s: State, status: Dict, route: List):
    plan = []
    #print(route)
    while route:
        temp = route.copy()
        current = temp[0]
        if current == s[HC.PIANO_WIRE][0]:
            plan.append("take_weapon")
        elif current == s[HC.SUIT][0]:
            plan.append("take_suit")
        elif current == s[HC.TARGET][0]:
            plan.append("kill_target")

        if (
            current not in s["vision_guard_civil"]
            and not status["is_suit_on"]
            and status["has_suit"]
        ):
            plan.append("put_on_suit")

        # Déplacements
        if len(temp) > 1:
            next = temp[1]

            # On gère le cas de la neutralisation
            # On s'est mis d'accord pour dire: 3 fois la position -> garde ; 2 fois -> civil

            guard_to_neutralize = False
            civil_to_neutralize = False

            # Garde
            if len(temp) == 4:
                next_next = temp[2]
                if current == next and next == next_next:
                    guard_to_neutralize = True
                    del route[3]
                    del route[2]
                    del route[1]

            # Civil
            elif len(temp) == 3:
                if current == next:
                    civil_to_neutralize = True
                    del route[2]
                    del route[1]

            if guard_to_neutralize or civil_to_neutralize:
                next = temp[-1]

            # même i
            if next[0] == current[0]:
                # turn_S
                if next[1] < current[1]:
                    plan.append("turn_S")
                    if guard_to_neutralize:
                        plan.append("neutralize_guard")
                    elif civil_to_neutralize:
                        plan.append("neutralize_civil")
                    plan.append("move_S")
                # turn_N
                if next[1] > current[1]:
                    plan.append("turn_N")
                    if guard_to_neutralize:
                        plan.append("neutralize_guard")
                    elif civil_to_neutralize:
                        plan.append("neutralize_civil")
                    plan.append("move_N")
            elif next[1] == current[1]:
                # turn_W
                if next[0] < current[0]:
                    plan.append("turn_W")
                    if guard_to_neutralize:
                        plan.append("neutralize_guard")
                    elif civil_to_neutralize:
                        plan.append("neutralize_civil")
                    plan.append("move_W")
                # turn_E
                if next[0] > current[0]:
                    plan.append("turn_E")
                    if guard_to_neutralize:
                        plan.append("neutralize_guard")
                    elif civil_to_neutralize:
                        plan.append("neutralize_civil")
                    plan.append("move_E")

        route.remove(current)
    return plan


def execute_plan(plan: Plan, s0: State, status: Dict, true_map: Dict):
    s = s0
    for action_id in plan:
        status, s = action_id_to_action[action_id](s, status)
        afficher_grille(m, n, true_map, status)
    return s


def solver_phase2(s: State, status: Dict, true_map: Dict):
    while not is_final(status, true_map, s):
        # Chemin de 0,0 jusqu'à la corde:
        i_wire, j_wire = s[HC.PIANO_WIRE][0]
        route_wire = establish_route(
            s,
            status,
            Node(i_wire, j_wire, 0, distance_manhattan((0, 0), (i_wire, j_wire))),
            Node(0, 0, 0, 0),
        )
        cout_route_wire = len(route_wire)

        # Chemin de 0,0 jusqu'au costume:
        i_suit, j_suit = s[HC.SUIT][0]
        route_suit = establish_route(
            s,
            status,
            Node(i_wire, j_wire, 0, distance_manhattan((0, 0), (i_suit, j_suit))),
            Node(0, 0, 0, 0),
        )
        cout_route_suit = len(route_suit)

        # Chemin de la corde jusqu'au costume et vice versa:
        route_wire_to_suit = establish_route(
            s,
            status,
            Node(
                i_suit,
                j_suit,
                0,
                distance_manhattan((i_wire, j_wire), (i_suit, j_suit)),
            ),
            Node(i_wire, j_wire, 0, 0),
        )
        cout_route_wire_to_suit = len(route_wire_to_suit)

        route_suit_to_wire = establish_route(
            s,
            status,
            Node(
                i_wire,
                j_wire,
                0,
                distance_manhattan((i_wire, j_wire), (i_suit, j_suit)),
            ),
            Node(i_suit, j_suit, 0, 0),
        )
        cout_route_suit_to_wire = len(route_suit_to_wire)

        # Chemin de la corde jusqu'à la cible
        i_target, j_target = s[HC.TARGET][0]
        route_wire_to_target = establish_route(
            s,
            status,
            Node(
                i_target,
                j_target,
                0,
                distance_manhattan((i_wire, j_wire), (i_target, j_target)),
            ),
            Node(i_wire, j_wire, 0, 0),
        )

        # Chemin du costume jusqu'à la cible
        route_suit_to_target = establish_route(
            s,
            status,
            Node(
                i_target,
                j_target,
                0,
                distance_manhattan((i_suit, j_suit), (i_target, j_target)),
            ),
            Node(i_suit, j_suit, 0, 0),
        )

        # Chemin de la cible vers 0,0
        route_target_to_exit = establish_route(
            s,
            status,
            Node(0, 0, 0, distance_manhattan((0, 0), (i_target, j_target))),
            Node(i_target, j_target, 0, 0),
        )

        # Combinaison 1: 0,0 -> corde -> target -> 0,0
        # Combinaison 2: 0,0 -> costume -> corde -> target -> 0,0
        # Combinaison 3: 0,0 -> corde -> costume -> target -> 0,0

        combinaison_1 = [route_wire, route_wire_to_target, route_target_to_exit]
        combinaison_2 = [
            route_suit,
            route_suit_to_wire,
            route_wire_to_target,
            route_target_to_exit,
        ]
        combinaison_3 = [
            route_wire,
            route_wire_to_suit,
            route_suit_to_target,
            route_target_to_exit,
        ]

        cout_combinaison1 = sum(len(liste) for liste in combinaison_1)
        cout_combinaison2 = sum(len(liste) for liste in combinaison_2)
        cout_combinaison3 = sum(len(liste) for liste in combinaison_3)

        combinaisons_with_cout = {
            1: cout_combinaison1,
            2: cout_combinaison2,
            3: cout_combinaison3,
        }

        # Ajouter le nombre de pénalité qu'on aura si on passe dans la vision des gardes sans costume
        combinaison_to_search = []
        for combinaison, cout in combinaisons_with_cout.items():
            danger = 0
            if combinaison == 1:
                combinaison_to_search = combinaison_1
            elif combinaison == 2:
                combinaison_to_search = combinaison_2
            elif combinaison == 3:
                combinaison_to_search = combinaison_3
            for route in combinaison_to_search:
                if route != route_suit_to_wire and route != route_suit_to_target:
                    for pos in route:
                        if (pos[0], pos[1]) in s["vision_guard"]:
                            danger += 5
            combinaisons_with_cout[combinaison] += danger

        combinaisons_with_cout = sorted(
            combinaisons_with_cout.items(), key=lambda x: x[1]
        )
        #pprint(combinaisons_with_cout)
        number_route_to_follow = next(iter(combinaisons_with_cout))
        route_to_follow = []
        if number_route_to_follow[0] == 1:
            route_to_follow = combinaison_1
        elif number_route_to_follow[0] == 2:
            route_to_follow = combinaison_2
        elif number_route_to_follow[0] == 3:
            route_to_follow = combinaison_3

        neutralize = False
        # On détermine si on doit neutraliser
        if (i_target, j_target) in s["vision_guard_civil"]:
            neutralize = True  # On détermine si on doit neutraliser
            #print(neutralize)

        i, j = status["position"]
        # Gestion de la fin : on a l'arme (et peut être le costume) et on veut aller tuer la target mais avant : il faut neutraliser potentiellement

        if neutralize:
            i_n, j_n = s["a_neutraliser"][0]  # tuple (i,j)
            route_to_neutralize = []
            # On cherche
            spot_number = 0
            #                         E                 N                W                S
            spot_to_neutralize = [
                (i_n + 1, j_n),
                (i_n, j_n + 1),
                (i_n - 1, j_n),
                (i_n, j_n - 1),
            ]

            fumier = s["a_neutraliser"][0]
            # Je supprime le spot qui est dans la vision direct du civil/garde
            if fumier in s[HC.GUARD_S] or fumier in s[HC.CIVIL_S]:
                # si il regarde au sud, je dégage la case au sud d'office
                del spot_to_neutralize[3]
            elif fumier in s[HC.GUARD_N] or fumier in s[HC.CIVIL_N]:
                del spot_to_neutralize[1]
            elif fumier in s[HC.GUARD_E] or fumier in s[HC.CIVIL_E]:
                del spot_to_neutralize[0]
            elif fumier in s[HC.GUARD_W] or fumier in s[HC.CIVIL_W]:
                del spot_to_neutralize[2]

            for spot in spot_to_neutralize.copy():
                if (
                    spot[0] >= n
                    or spot[0] < 0
                    or spot[1] >= m
                    or spot[1] < 0
                    or spot in s["vision_guard_civil"]
                ):
                    spot_to_neutralize.remove(spot)
            selected_spot = spot_to_neutralize[spot_number]
            max_spot = len(spot_to_neutralize) - 1

            guard_to_neutralize = False
            if (
                fumier in s[HC.GUARD_S]
                or fumier in s[HC.GUARD_N]
                or fumier in s[HC.GUARD_E]
                or fumier in s[HC.GUARD_W]
            ):
                guard_to_neutralize = True

            if number_route_to_follow[0] == 1 or number_route_to_follow[0] == 2:
                # Dans ce cas, on cherche un chemin de la corde à une case adjacente de la position à neutraliser.
                route_wire_to_neutralize_spot = establish_route(
                    s,
                    status,
                    Node(
                        selected_spot[0],
                        selected_spot[1],
                        0,
                        distance_manhattan(
                            (i_wire, j_wire), (selected_spot[0], selected_spot[1])
                        ),
                    ),
                    Node(i_wire, j_wire, 0, 0),
                )
                while route_wire_to_neutralize_spot is None:
                    spot_number += 1
                    if spot_number > max_spot:
                        print("Erreur max_spot reached")
                        break
                    selected_spot = spot_to_neutralize[spot_number]
                    route_wire_to_neutralize_spot = establish_route(
                        s,
                        status,
                        Node(
                            selected_spot[0],
                            selected_spot[1],
                            0,
                            distance_manhattan(
                                (i_wire, j_wire), (selected_spot[0], selected_spot[1])
                            ),
                        ),
                        Node(i_wire, j_wire, 0, 0),
                    )

                # On ajoute 2 ou 3 fois la coordonnée pour transmettre au convert_route_to_plan si on doit neutraliser un civil ou un garde
                if guard_to_neutralize:
                    route_wire_to_neutralize_spot.append(
                        route_wire_to_neutralize_spot[-1]
                    )
                route_wire_to_neutralize_spot.append(route_wire_to_neutralize_spot[-1])

                # On ajoute la personne à neutraliser pour faire comprendre à convert_route_to_plan
                route_wire_to_neutralize_spot.append(fumier)

                route_to_follow[-2] = route_wire_to_neutralize_spot

            elif number_route_to_follow[0] == 3:
                route_suit_to_neutralize_spot = establish_route(
                    s,
                    status,
                    Node(
                        selected_spot[0],
                        selected_spot[1],
                        0,
                        distance_manhattan(
                            (i_suit, j_suit), (selected_spot[0], selected_spot[1])
                        ),
                    ),
                    Node(i_suit, j_suit, 0, 0),
                )
                while route_suit_to_neutralize_spot is None:
                    spot_number += 1
                    if spot_number > max_spot:
                        print("Erreur max_spot reached")
                        break
                    selected_spot = spot_to_neutralize[spot_number]
                    route_suit_to_neutralize_spot = establish_route(
                        s,
                        status,
                        Node(
                            selected_spot[0],
                            selected_spot[1],
                            0,
                            distance_manhattan(
                                (i_suit, j_suit), (selected_spot[0], selected_spot[1])
                            ),
                        ),
                        Node(i_suit, j_suit, 0, 0),
                    )

                # On ajoute 2 ou 3 fois la coordonnée pour transmettre au convert_route_to_plan si on doit neutraliser un civil ou un garde
                if guard_to_neutralize:
                    route_suit_to_neutralize_spot.append(
                        route_suit_to_neutralize_spot[-1]
                    )
                route_suit_to_neutralize_spot.append(route_suit_to_neutralize_spot[-1])

                # On ajoute la personne à neutraliser pour faire comprendre à convert_route_to_plan
                route_suit_to_neutralize_spot.append(fumier)
                route_to_follow[-2] = route_suit_to_neutralize_spot

            route_neutralize_spot_to_target = establish_route(
                s,
                status,
                Node(
                    i_target,
                    j_target,
                    0,
                    distance_manhattan(
                        (selected_spot[0], selected_spot[1]), (i_target, j_target)
                    ),
                ),
                Node(selected_spot[0], selected_spot[1], 0, 0),
            )
            #print("ROUTE NEUTRALIZE TO TARGET", route_neutralize_spot_to_target)
            route_to_follow.insert(-1, route_neutralize_spot_to_target)

        # Fonctionne ! Si on a pas a neutraliser, on exécute directement le plan.
        plan = []
        for route in route_to_follow:
            plan += convert_route_to_plan(s, status, route)
        #print("PLAN: ", plan)
        s = execute_plan(plan, s, status, true_map)


def main():
    # ---------- PHASE 1 ----------
    print("\n--------- PHASE 1 ---------\n")
    time.sleep(3)
    status = hr.start_phase1()
    global m, n, nbVar, nbVar_reel
    m = status["m"]
    n = status["n"]
    nbVar = len(HC)
    nbVar_reel = m * n * nbVar
    #print(status)
    map = set_empty_map()
    solver_phase1(status, map)
    pprint(hr.send_content(map))
    _, score, history, true_map = hr.end_phase1()
    print(score)
    time.sleep(10)
    # ---------- PHASE 2 ----------
    print("\n--------- PHASE 2 ---------\n")
    time.sleep(3)
    status = hr.start_phase2()

    s0 = initial_state(status, true_map)
    #pprint(s0)
    solver_phase2(s0, status, true_map)
    _, score, history = hr.end_phase2()
    print("\nRécapitulatif des mouvements de la phase 2 : \n")
    print(history)
    print("\n")
    print(score)


if __name__ == "__main__":
    main()
