import matplotlib.pyplot as plt
from matplotlib.animation import FuncAnimation
import math
import random
import time
import sys

def timing_decorator(func):
    def wrapper(*args, **kwargs):
        start_time = time.time()
        result = func(*args, **kwargs)
        end_time = time.time()
        execution_time = end_time - start_time
        print(f'{func.__name__} executed in {execution_time:.2f} seconds')
        return result
    return wrapper


class TSPInstance:
    def __init__(self, file_path):
        self.cities = []  # List to store City objects
        self.load_instance(file_path)

    def load_instance(self, file_path):
        try:
            with open(file_path, 'r') as file:
                n = int(file.readline().strip())
                for _ in range(n):
                    id, x, y = map(int, file.readline().split())
                    self.cities.append((id, x, y))
        except FileNotFoundError:
            print(f"File '{file_path}' not found.")
            self.cities = []

    def plot_cities(self):
        x = [city[1] for city in self.cities]
        y = [city[2] for city in self.cities]

        plt.figure(figsize=(8, 6))
        plt.scatter(x, y, marker='o', color='red', label='Cities')
        plt.xlabel('X Coordinate')
        plt.ylabel('Y Coordinate')
        plt.title('Cities on 2D Map')
        plt.legend()
        plt.grid(True)

    def calculate_distance(self, city1, city2):
        x1, y1 = city1[1], city1[2]
        x2, y2 = city2[1], city2[2]
        return math.sqrt((x1 - x2) ** 2 + (y1 - y2) ** 2)

    def plot_tour(self, tour):
        self.plot_cities()

        x = [city[1] for city in self.cities]
        y = [city[2] for city in self.cities]

        # Corrected code to use city IDs to index self.cities
        tour_x = [x[self.cities[city - 1][0] - 1] for city in tour]
        tour_y = [y[self.cities[city - 1][0] - 1] for city in tour]

        plt.plot(tour_x, tour_y, linestyle='-', color='blue', marker='o', markersize=5, label='Tour')
        plt.xlabel('X Coordinate')
        plt.ylabel('Y Coordinate')
        plt.title('TSP Tour')
        plt.legend()
        plt.grid(True)

        total_distance = 0
        for i in range(len(tour) - 1):
            total_distance += self.calculate_distance(self.cities[tour[i] - 1], self.cities[tour[i + 1] - 1])
        total_distance += self.calculate_distance(self.cities[tour[-1] - 1], self.cities[tour[0] - 1])

        print(f'Total Distance of the Tour: {total_distance:.2f} km')
        plt.show()


class MH:
    def __init__(self, tsp_instance):
        self.tsp_instance = tsp_instance
        self.current_tour = self.generate_initial_solution()
        self.current_distance = self.calculate_tour_distance(self.current_tour)

    def generate_initial_solution(self):
        city_ids = [city[0] for city in self.tsp_instance.cities]
        random.shuffle(city_ids)
        return city_ids

    def calculate_tour_distance(self, tour):
        total_distance = 0
        for i in range(len(tour) - 1):
            total_distance += self.tsp_instance.calculate_distance(
                self.tsp_instance.cities[tour[i] - 1],
                self.tsp_instance.cities[tour[i + 1] - 1]
            )
        total_distance += self.tsp_instance.calculate_distance(
            self.tsp_instance.cities[tour[-1] - 1],
            self.tsp_instance.cities[tour[0] - 1]
        )
        return total_distance

    def hill_climbing(self, max_iterations):
        for iteration in range(max_iterations):
            neighbors = self.get_neighbor_solutions()
            best_neighbor = min(neighbors, key=lambda tour: self.calculate_tour_distance(tour))

            if self.calculate_tour_distance(best_neighbor) < self.current_distance:
                self.current_tour = best_neighbor
                self.current_distance = self.calculate_tour_distance(best_neighbor)
            else:
                # Stuck in a local minimum
                break

    def get_neighbor_solutions(self):
        neighbors = []
        for i in range(len(self.current_tour)):
            for j in range(i + 1, len(self.current_tour)):
                neighbor = self.current_tour[:]
                neighbor[i], neighbor[j] = neighbor[j], neighbor[i]
                neighbors.append(neighbor)
        return neighbors

    def get_best_tour(self):
        return self.current_tour

    def get_best_distance(self):
        return self.current_distance
    
    def hill_climbing_step(self):
        best_improvement = float('inf')
        best_neighbor = None
        best_swapped_indices = None

        for i in range(len(self.current_tour)):
            for j in range(i + 1, len(self.current_tour)):
                neighbor = self.current_tour[:]
                neighbor[i], neighbor[j] = neighbor[j], neighbor[i]
                improvement = self.calculate_tour_distance(neighbor) - self.current_distance

                if improvement < best_improvement:
                    best_improvement = improvement
                    best_neighbor = neighbor
                    best_swapped_indices = (i, j)

        if best_neighbor and best_improvement < 0:
            self.current_tour = best_neighbor
            self.current_distance += best_improvement
            return best_swapped_indices

        return None

    def animate_hill_climbing(self, max_iterations):
        fig, ax = plt.subplots()
        x = [city[1] for city in self.tsp_instance.cities]
        y = [city[2] for city in self.tsp_instance.cities]
        line, = ax.plot([], [], linestyle='-', color='blue', marker='o')
        main_cities_scatter = ax.scatter(x, y, color='blue', s=50)  # Main cities in blue
        swapped_cities_scatter = ax.scatter([], [], color='red', s=100)  # Swapped cities in red
        distance_text = ax.text(0.5, 0.98, '', transform=ax.transAxes, ha='center', fontsize=12, va='top')

        def init():
            ax.set_xlabel('X Coordinate')
            ax.set_ylabel('Y Coordinate')
            ax.grid(True)
            return line, distance_text, main_cities_scatter, swapped_cities_scatter

        def update(iteration):
            swapped_indices = None
            if iteration < max_iterations:
                swapped_indices = self.hill_climbing_step()
                if swapped_indices is None:
                    return line, distance_text, main_cities_scatter, swapped_cities_scatter

            current_tour = self.current_tour
            tour_x = [x[self.tsp_instance.cities[city - 1][0] - 1] for city in current_tour]
            tour_y = [y[self.tsp_instance.cities[city - 1][0] - 1] for city in current_tour]
            line.set_data(tour_x, tour_y)

            if swapped_indices:
                swapped_x = [tour_x[idx] for idx in swapped_indices]
                swapped_y = [tour_y[idx] for idx in swapped_indices]
                swapped_cities_scatter.set_offsets(list(zip(swapped_x, swapped_y)))

            total_distance = self.calculate_tour_distance(current_tour)
            distance_text.set_text(f'Total Distance: {total_distance:.2f} km')

            ax.set_title(f'TSP Tour - Iteration {iteration}')
            return line, distance_text, main_cities_scatter, swapped_cities_scatter

        ani = FuncAnimation(fig, update, frames=max_iterations, init_func=init, blit=True, repeat=False)
        plt.show()



if len(sys.argv) != 2:
    print("Rajouter l'argument du path du fichier --> Utilisation : python salesman-animated.py <nom-fichier>")
    sys.exit(1)

# Récupérer le nom du fichier à partir des arguments de la ligne de commande
file_path = sys.argv[1]

tsp_instance = TSPInstance(file_path)
mh_solver = MH(tsp_instance)

# Perform Hill Climbing with a maximum number of iterations and visualize the progress
max_iterations = 1000
mh_solver.animate_hill_climbing(max_iterations)

# Get the best tour and its distance
best_tour = mh_solver.get_best_tour()
best_distance = mh_solver.get_best_distance()

print(f'Best Tour: {best_tour}')
print(f'Best Distance: {best_distance:.2f} km')