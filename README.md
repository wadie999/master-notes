# Travelling Salesman Problem (TSP) Project

## Introduction
This project is dedicated to solving the famous Travelling Salesman Problem (TSP), an important problem in combinatorial optimization. The TSP involves finding the shortest possible route that visits a set of cities and returns to the origin city. The focus of this project is to implement and analyze various metaheuristic approaches for solving the TSP.

## Problem Description
In the TSP, we are given a set of cities and the distances between each pair of cities. The challenge is to find the shortest possible tour that visits each city exactly once and returns to the starting city. This project will use a set of city coordinates provided in text files, and the goal is to minimize the total tour distance.

## Approaches
We will employ several metaheuristic techniques to tackle the TSP, including:

1. **Random Initial Solution Generation**: Generating a random tour as a starting point.
2. **Hill Climbing**: Iteratively improving the solution by making local changes.
3. **Steepest Hill Climbing**: Choosing the best move at each step for improvement.
4. **Hill Climbing with Restarts**: Enhancing exploration by restarting the process from different initial solutions.
5. **Tabu Search**: Using memory structures to avoid revisiting recently explored solutions.

## Exercises and Implementation
The project will include exercises for implementing these techniques:

1. **Random Tour Generation**: Writing a function to generate a random tour of cities.
2. **Tour Evaluation**: Developing a function to calculate the total distance of a tour.
3. **Neighborhood Operations**: Implementing functions to explore neighboring tours, including 2-swap and 2-opt moves.
4. **Hill Climbing Implementations**: Writing functions for hill climbing and steepest hill climbing approaches.
5. **Restart Mechanisms**: Developing a hill climbing variant with restarts.
6. **Tabu Search**: Implementing the tabu search method with varying list sizes.

Each of these exercises will contribute to building a comprehensive solution for the TSP using different metaheuristic approaches.

## Getting Started
To get started with this project, clone the repository, and follow the instructions in the individual exercise folders. The project is structured to guide you through each step of solving the TSP using metaheuristics.

## Contributing
Contributions to this project are welcome. Please read the contributing guidelines before making a pull request.

## License
This project is licensed under the MIT License - see the LICENSE file for details.
