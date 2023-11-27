import numpy as np
import sys
import math
import random
import matplotlib.pyplot as plt
import time
from mpi4py import MPI
ID, POSX, POSY, SPEEDX, SPEEDY, WEIGHT = range(6)
random.seed(0)  # Replace 0 with your chosen seed

solarmass=1.98892e30
def circlev(rx, ry):
    r2=math.sqrt(rx*rx+ry*ry)
    numerator=(6.67e-11)*1e6*solarmass
    return math.sqrt(numerator/r2)
# from http://physics.princeton.edu/~fpretori/Nbody/code.htm
def create_item(id, positionx, positiony, speedx, speedy, weight):
    if positionx == 0 and positiony == 0:  # the center of the world, very heavy one...
        speedx = 0
        speedy = 0
    else:
        if speedx==0 and speedy==0:            # initial values
            magv=circlev(positionx, positiony)
            absangle = math.atan(math.fabs(positiony/positionx))
            thetav= math.pi/2-absangle
            phiv = random.uniform(0,1)*math.pi
            speedx = -1*math.copysign(1, positiony)*math.cos(thetav)*magv
            speedy = math.copysign(1, positionx)*math.sin(thetav)*magv
            #Orient a random 2D circular orbit
            if (random.uniform(0,1) <=.5):
                speedx=-speedx
                speedy=-speedy
    return np.array([id, positionx, positiony, speedx, speedy, weight], dtype='f')

def str_item(item):
    return "ID="+str(item[ID])+" POS=("+str(item[POSX])+","+str(item[POSY])+") SPEED=("+str(item[SPEEDX])+","+str(item[SPEEDY])+") WEIGHT="+str(item[WEIGHT])

def display(m, l):
    for i in range(len(l)):
        print("PROC"+str(rank)+":"+m+"-"+str_item(l[i]))

def displayPlot(d):
    plt.gcf().clear()
    plt.axis((-1e17, 1e17, -1e17, 1e17))

    # Plot all bodies in red except for the central body
    for body in d:
        if body[ID] == len(d) - 1:  # Check if it's the central body
            plt.plot(body[POSX], body[POSY], 'bo')  # Plot central body in blue
        else:
            plt.plot(body[POSX], body[POSY], 'ro')  # Plot other bodies in red

    plt.draw()
    plt.pause(0.00001)


def interaction(i, j):
    dist = math.sqrt( (j[POSX]-i[POSX])*(j[POSX]-i[POSX]) +  (j[POSY]-i[POSY])*(j[POSY]-i[POSY]) )
    if dist == 0:
        return np.zeros(2)
    g = 6.673e-11
    factor = g * i[WEIGHT] * j[WEIGHT] / (dist*dist+3e4*3e4)
    return np.array([factor*(j[POSX]-i[POSX])/dist, factor*(j[POSY]-i[POSY])/dist])

def update(d, f):
    dt = 1e11
    vx = d[SPEEDX] + dt * f[0]/d[WEIGHT]
    vy = d[SPEEDY] + dt * f[1]/d[WEIGHT]
    px = d[POSX] + dt * vx
    py = d[POSY] + dt * vy
    return create_item(d[ID], positionx=px, positiony=py, speedx=vx, speedy=vy, weight=d[WEIGHT])

def signature(world):
    s = 0
    for d in world:
        s+=d[POSX]+d[POSY]
    return s

def init_world(n):
    data = [ create_item(id=i, positionx=1e18*math.exp(-1.8)*(.5-random.uniform(0,1)), positiony=1e18*math.exp(-1.8)*(.5-random.uniform(0,1)), speedx=0, speedy=0, weight=(random.uniform(0,1)*solarmass*10+1e20)) for i in range(n-1)]
    data.append( create_item(id=n-1, positionx=0, positiony=0, speedx=0, speedy=0, weight=1e6*solarmass))
    return np.array(data)


# Initialize MPI
comm = MPI.COMM_WORLD
size = comm.Get_size()
rank = comm.Get_rank()

# Command-line arguments for number of bodies and steps
n_bodies = int(sys.argv[1])
n_steps = int(sys.argv[2])

# Determine the size of each local chunk
local_n = n_bodies // size
all_data = np.empty((n_bodies, 6), dtype='f')

# Prepare a local array to receive the scattered data
local_data = np.empty((local_n, 6), dtype='f')

# Scatter the data from the root process to all processes
if rank == 0:
    init_data = init_world(n_bodies)
else:
    init_data = None
comm.Scatter(init_data, local_data, root=0)
start_time = time.time()
for t in range(n_steps):
    # Synchronize all_data before force calculation
    comm.Allgather(local_data, all_data)

    # Step 3: Force Calculation
    local_force = np.zeros((local_n, 2))
    for i in range(local_n):
        for j in range(n_bodies):
            if rank * local_n + i != j:  # Avoid self-interaction
                local_force[i] += interaction(local_data[i], all_data[j])

    # Step 4: Data Update
    for i in range(local_n):
        local_data[i] = update(local_data[i], local_force[i])

    # Synchronize updated local_data across all processes
    comm.Allgather(local_data, all_data)

# Step 6: Output and Iteration
# Gather data at root for final output or further processing
final_data = np.empty((n_bodies, 6), dtype='f') if rank == 0 else None
comm.Gather(local_data, final_data, root=0)
end_time = time.time()
if rank == 0:
    print(end_time - start_time )
    print(signature(final_data))


