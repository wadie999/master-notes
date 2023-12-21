import matplotlib.pyplot as plt
import itertools
import math

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

    def display_cities(self):
        for city in self.cities:
            print(f"City {city[0]}: ({city[1]}, {city[2]})")

    def display_tour(self, tour):
        for city_id in tour:
            city = next((c for c in self.cities if c[0] == city_id), None)
            if city:
                print(f"City {city[0]}: ({city[1]}, {city[2]})")
            else:
                print(f"City {city_id} not found in the instance.")

# Example usage:
file_path = 'tsp5.txt'
tsp_instance = TSPInstance(file_path)

# Display cities
tsp_instance.display_cities()

# Example tour (replace with your own tour)
tour = [1, 2, 3, 4, 5]

# Display tour
tsp_instance.display_tour(tour)
