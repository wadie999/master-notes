import random
import math
import time
import os

class City:
    def __init__(self, city_id, x, y):
        self.city_id = city_id
        self.x = x
        self.y = y

    def distance_to(self, other_city):
        return math.sqrt((self.x - other_city.x) ** 2 + (self.y - other_city.y) ** 2)

class TSPSolver:
    def __init__(self, file_path, neighborhood_method):
        self.cities = self.load_cities(file_path)
        self.neighborhood_method = neighborhood_method
        self.starting_point = City(0, 0, 0)
        self.current_tour = self.generate_random_solution()
        self.current_distance = self.calculate_solution_value(self.current_tour)
        self.solutions_visited = 0
        self.iteration_data = []

    def load_cities(self, file_path):
        cities = []
        with open(file_path, 'r') as file:
            n = int(file.readline().strip())
            for _ in range(n):
                city_id, x, y = map(int, file.readline().split())
                cities.append(City(city_id, x, y))
        return cities

    def generate_random_solution(self):
        tour = list(range(1, len(self.cities) + 1))
        random.shuffle(tour)
        return tour

    def calculate_solution_value(self, solution):
        total_distance = 0
        previous_city = self.starting_point
        for city_id in solution:
            current_city = self.cities[city_id - 1]
            total_distance += previous_city.distance_to(current_city)
            previous_city = current_city
        total_distance += previous_city.distance_to(self.starting_point)
        return total_distance

    def get_neighbor_solutions(self, current_tour):
        neighbors = []
        for i in range(len(current_tour)):
            for j in range(i + 1, len(current_tour)):
                neighbor = current_tour[:]
                if self.neighborhood_method == '2-swap':
                    neighbor[i], neighbor[j] = neighbor[j], neighbor[i]
                elif self.neighborhood_method == '2-opt':
                    neighbor = neighbor[:i] + neighbor[i:j][::-1] + neighbor[j:]
                neighbors.append(neighbor)
        return neighbors

    def best_neighbor(self, current_tour):
        neighbors = self.get_neighbor_solutions(current_tour)
        self.solutions_visited += len(neighbors)
        best_neighbor = min(neighbors, key=self.calculate_solution_value)
        best_neighbor_distance = self.calculate_solution_value(best_neighbor)

        return best_neighbor, best_neighbor_distance

    def steepest_hill_climbing(self, max_iterations):
        self.current_tour = self.generate_random_solution()
        self.current_distance = self.calculate_solution_value(self.current_tour)
        self.solutions_visited = 0

        iteration_data = []  # Store iteration data

        for iteration in range(max_iterations):
            neighbor, neighbor_distance = self.best_neighbor(self.current_tour)

            iteration_data.append(self.current_distance)

            if neighbor_distance < self.current_distance:
                self.current_tour = neighbor
                self.current_distance = neighbor_distance
            else:
                # Log when a local minimum is reached
                print(f"Local minimum reached at iteration {iteration}")
                break  # This could be happening early
            self.solutions_visited += 1

        return self.current_tour, self.current_distance, self.solutions_visited, iteration_data

        


    def steepest_hill_climbing_with_restarts(self, max_restarts, max_iterations):
        best_tour = None
        best_distance = float('inf')
        total_solutions_visited = 0
        restarts_summary = []

        for restart in range(max_restarts):
            self.current_tour = self.generate_random_solution()
            initial_tour = self.current_tour[:]
            initial_distance = self.calculate_solution_value(initial_tour)
            self.current_distance = initial_distance
            self.solutions_visited = 0

            iteration_data = []  # Store iteration data for this restart

            for iteration in range(max_iterations):
                neighbor, neighbor_distance = self.best_neighbor(self.current_tour)

                # Record the distance every 100 visits
                if self.solutions_visited % 100 == 0:
                    iteration_data.append(neighbor_distance)

                if neighbor_distance < self.current_distance:
                    self.current_tour = neighbor
                    self.current_distance = neighbor_distance
                else:
                    print(f"Local minimum reached at iteration {iteration}")
                    break  # Local minimum reached

                self.solutions_visited += 1

            total_solutions_visited += self.solutions_visited
            restarts_summary.append({
                'restart': restart,
                'initial_tour': initial_tour,
                'initial_distance': initial_distance,
                'final_tour': self.current_tour,
                'final_distance': self.current_distance,
                'solutions_visited': self.solutions_visited,
                'iteration_data': iteration_data  # Include iteration data
            })

            if self.current_distance < best_distance:
                best_tour = self.current_tour
                best_distance = self.current_distance

        return best_tour, best_distance, total_solutions_visited, restarts_summary



    def tabu_search(self, max_moves, tabu_size):
        tabu_list = []
        best_tour = self.current_tour
        best_distance = self.calculate_solution_value(best_tour)

        for move in range(max_moves):
            start_time = time.time()
            neighbors = self.get_neighbor_solutions(self.current_tour)
            neighbors = [n for n in neighbors if n not in tabu_list]

            current_best_neighbor = min(neighbors, key=self.calculate_solution_value)
            current_best_distance = self.calculate_solution_value(current_best_neighbor)

            if current_best_distance < best_distance:
                best_tour = current_best_neighbor
                best_distance = current_best_distance

            tabu_list.append(current_best_neighbor)
            if len(tabu_list) > tabu_size:
                tabu_list.pop(0)

            self.solutions_visited += len(neighbors)
            self.iteration_data.append({
                'move': move,
                'distance': best_distance,
                'time': time.time() - start_time
            })

        return best_tour, best_distance, tabu_list

    def get_number_of_solutions_visited(self):
        return self.solutions_visited

    def get_iteration_data(self):
        return self.iteration_data

def clear_screen():
    os.system('cls' if os.name == 'nt' else 'clear')

def get_file_choice():
    files = ["tsp5.txt", "tsp25.txt", "tsp50.txt", "tsp101.txt"]
    for i, file in enumerate(files, 1):
        print(f"{i} - {file}")
    choice = int(input("What file do you want to test? Please give the number of the file: "))
    clear_screen()
    return files[choice - 1]

def get_neighborhood_choice():
    print("1 - 2-opt")
    print("2 - 2-swap")
    choice = int(input("Which kind of neighborhood do you want to use? "))
    clear_screen()
    return '2-opt' if choice == 1 else '2-swap'

# Assuming TSPSolver and get_file_choice, get_neighborhood_choice are already defined

def main():
    # File and neighborhood selection
    file_choice = get_file_choice()
    neighborhood_choice = get_neighborhood_choice()

    # Initialize the TSP solver
    tsp_solver = TSPSolver(file_choice, neighborhood_choice)

    # Taboo list decision
    use_taboo = input("Do you want to use a taboo list? (yes/no): ").strip().lower()
    if use_taboo == 'yes':
        tabu_size = int(input("Enter the size of the taboo list: "))
        best_tour_with_taboo, best_distance_with_taboo, solutions_visited_taboo, _ = tsp_solver.tabu_search(max_moves=1000, tabu_size=tabu_size)
        print(f"Taboo List Result:")
        print(f"Best Tour: {best_tour_with_taboo}")
        print(f"Best Distance: {best_distance_with_taboo:.2f}")
        print(f"Solutions Visited: {solutions_visited_taboo}\n")
    else:
        # Simple hill climbing execution
        initial_tour = tsp_solver.generate_random_solution()
        initial_distance = tsp_solver.calculate_solution_value(initial_tour)
        print(f"Initial Tour: {initial_tour}")
        print(f"Initial Distance: {initial_distance:.2f}")

        best_tour, best_distance, solutions_visited, _ = tsp_solver.steepest_hill_climbing(max_iterations=1000)
        print(f"Final Tour after Hill Climbing: {best_tour}")
        print(f"Final Distance: {best_distance:.2f}")
        print(f"Solutions Visited: {solutions_visited}\n")

    # Hill climbing with restarts decision
    use_restarts = input("Do you want to perform hill climbing with restarts? (yes/no): ").strip().lower()
    if use_restarts == 'yes':
        max_restarts = int(input("How many restarts would you like to perform? "))
        _, _, total_solutions_visited, restarts_summary = tsp_solver.steepest_hill_climbing_with_restarts(max_restarts, 1000)

        best_restart_info = {'final_distance': float('inf')}
        for restart_info in restarts_summary:
            print(f"\nRestart {restart_info['restart']}:")
            print(f"Initial Tour: {restart_info['initial_tour']}")
            print(f"Initial Distance: {restart_info['initial_distance']:.2f}")
            print(f"Final Tour: {restart_info['final_tour']}")
            print(f"Final Distance: {restart_info['final_distance']:.2f}")
            print(f"Solutions Visited: {restart_info['solutions_visited']}")

            if restart_info['final_distance'] < best_restart_info['final_distance']:
                best_restart_info = restart_info

        # Summary of the best restart
        print(f"\nBest Restart Summary:")
        print(f"Restart Number: {best_restart_info['restart']}")
        print(f"Initial Tour: {best_restart_info['initial_tour']}")
        print(f"Initial Distance: {best_restart_info['initial_distance']:.2f}")
        print(f"Best Tour: {best_restart_info['final_tour']}")
        print(f"Best Distance: {best_restart_info['final_distance']:.2f}")
        print(f"Total Solutions Visited: {total_solutions_visited}")

if __name__ == "__main__":
    main()

