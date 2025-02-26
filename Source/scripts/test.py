# libraries
#from matplotlib import pyplot as plt
import numpy as np
#import pandas as pd


import argparse

if __name__ == "__main__":
    parser = argparse.ArgumentParser(
        description="Script that adds 3 numbers from CMD"
    )
    parser.add_argument("--file", required=True, type=str)
    parser.add_argument("-x", required=True, type=str)
    parser.add_argument("-y", required=True, type=str)
    parser.add_argument("--sst", required=True, type=str)
    args = parser.parse_args()

    filename = args.file
    xAxis = args.x
    yAxis = args.y
    #arr2 = np.array( [ arr for arr in args.sst.split(':') ] )
    
    arr = args.sst.split(':')
    arr2 = []


    #arr2 = np.array( [ float(r) for r.split(',') in arr ] )
    #print(arr)
    #print(arr2)


    #arr = np.array([float(i) for i in args.sst.split(',')]) 
    for x in arr:
        #print(x)
        r = np.array([float(i) for i in x.split(',')])
        #print(x)
        arr2.append(r)

    print(arr2)
    #print(arr2[1])

    #1,2,3:2,4,6