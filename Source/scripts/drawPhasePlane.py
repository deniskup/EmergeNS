# libraries
from matplotlib import pyplot as plt
import numpy as np
import pandas as pd
import argparse




# calculate trajectory length represented by arrays (xaar, yarr)
def calculate_trajectory_length(xarr, yarr):
  l = 0.
  for i in range(len(xarr)-1):
    l += np.sqrt( (xarr[i+1]-xarr[i])*(xarr[i+1]-xarr[i]) + (yarr[i+1]-yarr[i])*(yarr[i+1]-yarr[i]) )
  return l

 # get clever positions of arrows along the trajectory (xarr, yarr)
# narr = number of arrows desired to show
def get_clever_arrow_pos(xarr, yarr, narr):

  #print("traj. array length = ", xarr.size)
  # get trajectory length
  l = calculate_trajectory_length(xarr, yarr)


  # length threshold after which an arrow should be drawn
  lth = l / (narr + 0.2)
  #print("traj. length = ", l, " ; l_th = ", lth)

  # parse trajectory and store positions in which arrows should be drawn
  # init some stuff
  currentL = 0.
  xprev = xarr[0]
  yprev = yarr[0]
  c1 = -1
  c2 = 0
  arraypos = np.zeros(narr, dtype=int)
  # start loop
  for (x, y) in zip(xarr, yarr):
    c1 += 1
    # update length w.r.t to previous point
    currentL +=  np.sqrt( (x-xprev)*(x-xprev) + (y-yprev)*(y-yprev) )
    xprev = x
    yprev = y
    # if length crosses threshold, store index position and re-init current length
    if (currentL > lth):
      #print("cross threshold for l = ", currentL, ". Save index ", c1, " at ", c2)
      arraypos[c2] = c1
      c2+=1
      currentL = 0.
  return arraypos





import argparse

# debugging command
# python3 drawPhasePlane.py --file ./concentrationDynamics_model4.csv -x '[A2]' -y '[B2]' --nruns 5 --sst ./steadyStates.csv


if __name__ == "__main__":
    parser = argparse.ArgumentParser(
        description="Script that adds 3 numbers from CMD"
    )
    # parse arguments
    parser.add_argument("--file", required=True, type=str)
    parser.add_argument("--nruns", required=True, type=int)
    parser.add_argument("-x", required=True, type=str)
    parser.add_argument("-y", required=True, type=str)
    parser.add_argument("--sst", required=True, type=str)
    args = parser.parse_args()

    # keep command line arguments in variables
    filename = args.file
    nruns = args.nruns
    xAxis = args.x
    yAxis = args.y
    steadyStateFile = args.sst

    # additionnal stuff
    narrows = 3
    skiprun = np.array([]) # keep this ?

    # read file data as dataframe
    df = pd.read_csv(filename)
    #df = pd.read_csv("./concentrationDynamics_model4.csv")
    dfsst = pd.read_csv(steadyStateFile)
    # separate gloablly and partially stable states
    dfsst_glob = dfsst[dfsst.isBorder==0]
    dfsst_part = dfsst[dfsst.isBorder==1]

    # for plot
    fig, ax = plt.subplots()

    # loop over runs
    c1=-1
    c2=-1
    xmax = 0.
    ymax = 0.
    for irun in range(nruns):

      #should skip run ?
      if len( np.where(skiprun == irun)[0] ):
        continue

      # only keep points associated to current run
      df_run = df[df.runID==irun]

      # check that run is non-empty
      if (df_run.shape[0]==0):
        print('run #', irun, ' is empty', '. Will not be drawn.')
        continue

      # get x and y concentrations vectors
      x = np.array(df_run[xAxis])
      y = np.array(df_run[yAxis])
      # calculate arrow positions to draw along the 2D trajectory
      arrowpos = get_clever_arrow_pos(x, y, narrows)

      # update max x and y axis values
      if np.max(x)>xmax:
        xmax = np.max(x)
      if np.max(y)>ymax:
        ymax = np.max(y)

      # plot the arrows
      for p in arrowpos:
        ax.annotate(xytext=(x[p], y[p]), xy=(x[p+1], y[p+1]), \
          arrowprops=dict(arrowstyle='->', mutation_scale=20), text='')

      # plot the 2D trajectory
      c1 += 1
      if c1==0:
        ax.plot(x, y, color='gray', label='Trajectory')
      else:
        ax.plot(x, y, color='gray')

      # plot the starting point
      c2 += 1
      if (c2==0):
        ax.scatter(x[0], y[0], color='black', marker='o', label='Start')
      else:
        ax.scatter(x[0], y[0], color='black', marker='o')

# plot steady state points
xsst_glob = np.array([dfsst_glob[xAxis]])[0]
ysst_glob = np.array([dfsst_glob[yAxis]])[0]
xsst_part = np.array([dfsst_part[xAxis]])[0]
ysst_part = np.array([dfsst_part[yAxis]])[0]

# plot globally stable states
c=-1
for stx, sty in zip(xsst_glob, ysst_glob):
  c+=1
  if c==0:
    ax.scatter(stx, sty, marker='*', color='black', label='Global Steady State', s=300)
  else:
    ax.scatter(stx, sty, marker='*', color='black', s=300)

# plot partially stable states 
c=-1
for stx, sty in zip(xsst_part, ysst_part):
  c+=1
  if c==0:
    ax.scatter(stx, sty, marker='*', color='white', edgecolor='black', \
     linewidth=1, label='Border Steady State', s=300)
  else:
    ax.scatter(stx, sty, marker='*', color='white', edgecolor='black', \
     linewidth=1, s=300)

  

# add extra margin
xmax += xmax/10.
ymax += ymax/10.

# add lines at x = 0 and y = 0
ax.plot( [0., 0.], [0., ymax], linestyle="dashed", color='gray' )
ax.plot( [0., xmax], [0., 0.], linestyle="dashed", color='gray' )

# add line at x = y
#lim = min(xmax, ymax)
#ax.plot( [0., lim], [0., lim], linestyle="dashed", color='gray' )

ax.set_xlabel(xAxis)
ax.set_ylabel(yAxis)
ax.set_xlim(-xmax/40., xmax)
ax.set_ylim(-ymax/40., ymax)
ax.legend()
plt.show()
