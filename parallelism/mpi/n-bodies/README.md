# N-Body Simulation Project
[Project Report](docs/nbodies-Report-ELAMRANI.pdf)

## Introduction
This project is centered around the N-Body problem, a classic problem in computational physics and astronomy. It involves simulating the motion of celestial bodies under the influence of gravitational forces. The project includes both sequential and parallel implementations, leveraging Python and MPI (Message Passing Interface) for parallel computing.

## Problem Description
The N-Body problem deals with predicting the motions of a group of celestial objects interacting with each other gravitationally. Our implementation focuses on:
- Calculating forces between bodies.
- Updating positions and velocities based on these forces.
- Visualizing the motion of these bodies over time.

## Sequential Implementation
The sequential version of the simulation is implemented in Python using NumPy for efficient array operations. It includes a step-by-step calculation of gravitational forces and motion updates.

### Key Components:
- **Force Calculation**: Computing gravitational forces between all pairs of bodies.
- **State Update**: Updating velocities and positions of each body based on the calculated forces.
- **Visualization**: Displaying the state of the system at each step of the simulation.

## Parallel Implementation with MPI
The parallel version uses MPI to distribute the computation across multiple processors, significantly improving performance for large numbers of bodies.

### Highlights:
- **MPI Initialization**: Setting up a parallel environment with MPI.
- **Data Partitioning**: Dividing the simulation data among processes.
- **Parallel Force Calculation**: Each process computes forces for a subset of bodies.
- **Synchronization**: Ensuring data consistency across processes.

## Usage
Instructions for running both sequential and parallel versions are included. The parallel version requires an MPI environment.

### Dependencies:
- Python 3
- NumPy
- MPI (for the parallel version)


## License
This project is open source and available under the MIT License.

