#import all the packages
import pandas as pd
from collections import deque
import sys
import itertools
from queue import PriorityQueue
import queue
import math
import copy
import time
import random
import errno
import os
import signal
import functools
import threading

def calculate_runtime(func):
    def wrapper(*args, **kwargs):
        start_time = time.time()
        result = func(*args, **kwargs)
        end_time = time.time()
        runtime = end_time - start_time
        return result, runtime
    return wrapper

#define Warehouse class
class Warehouse:
    #Class attributes
    max_x_index = 40
    max_y_index = 21
    worker_location = (0,0)
    drop_location   = (0, 0)
    debug_mode = "Disabled"
    input_file = None
    product_data = None
    shelf_info = None
    interface = None
    map = []
    products_to_collect = None
    export_to_file = "Disabled"
    algorithms_available = [
                                "Brute Force: Branch And Bound for TSP",
                                "Custom: Hill Climbing Algorithm for TSP",
                                "Nearest Neighbor First for TSP"
                            ]
    algorithm_selected = "Brute Force: Branch And Bound for TSP"
    timeout_interval = 60
    
    #Class methods
    def __init__(self, input_file): #initialize the class Warehouse object
        self.input_file = input_file
        self.get_product_data() #call the function to initialize the product
        self.get_shelf_info() #call the function to initialize the shelfs
        self.initialize_map() #call the function to initialize the map
        self.interface = Interface
        #decorate the algorithm functions with timeout decorator
        self.Branch_N_Bound = self.timeout(self.Branch_N_Bound)
        self.hillclimbing = self.timeout(self.hillclimbing)
        self.nearest_neighbor = self.timeout(self.nearest_neighbor)
    
    def timeout(self, func):
        def decorator(*args, **kwargs):
            result = [None]
            error = [None]
            
            def target():
                try:
                    result[0] = func(*args, **kwargs) #run function
                except Exception as e:
                    error[0] = e
            
            thread = threading.Thread(target=target)
            thread.daemon = True
            thread.start()
            thread.join(self.timeout_interval)
            
            if thread.is_alive(): #raise exception if timeout
                raise Exception
            
            if error[0] is not None:
                raise error[0]
            
            return result[0]

        return decorator
    
    def get_product_data(self): #Read the product data and store it in the product_data attribute
        self.product_data = pd.read_csv(self.input_file, sep="\t") #read input file
        self.product_data.set_index("ProductID", inplace=True)
    
    def initialize_map(self): #Create a map of the warehouse indicating where the shelves are located
        shelf_locations = []
        for productID, location in self.shelf_info.iterrows():
            shelf_locations.append((location["xLocation"], location["yLocation"]))
        for y_index in range(0,self.max_y_index):   
            row = []
            for x_index in range(self.max_x_index):
                if ((x_index, y_index) in shelf_locations): row.append(1) #Append 1 if shelf is present at the specified location
                else: row.append(0) #Append 0 if shelf is not present at the specified location
            self.map.append(row)
                
    def get_shelf_info(self): #Read the product data and store it in the shelf_info attribute
        df = self.product_data.copy(deep=True)
        df["xLocation"] = df["xLocation"].apply(lambda x: int(x))
        df["yLocation"] = df["yLocation"].apply(lambda x: int(x))
        df.drop_duplicates(inplace=True) #drop duplicate coordinates of the shelves
        self.shelf_info = df
    #get the location of the product from the product ID
    def get_product_location(self, product_id):
        xLocation = self.product_data["xLocation"][product_id]
        yLocation = self.product_data["yLocation"][product_id]
        return (xLocation, yLocation) #return the x and y coordinates of a product

    #BFS algorithm to find shortest path to get product
    def bfs_shortest_path(self, grid, source, destination):
        rmax = len(grid)
        cmax = len(grid[0])
        grid[destination[0]][destination[1]] = 0   
        q = deque([(source[0], source[1], [])]) # queues worker location and path
        visit = set(source)     #  stores visited nodes
        direction = [[1, 0], [0, 1], [0, -1], [-1, 0]]      #directions
        while q:
            r, c, path = q.popleft()
            if min(r, c) < 0 or r >= rmax or c >= cmax or grid[r][c] == 1:  #skip if out of bounds or shelf
                continue
            if r == destination[0] and c == destination[1]:     # end if reached shelf
                path.append((c, r))
                return path
            for dr, dc in direction:
                if (r + dr, c + dc) not in visit:
                    q.append((r + dr, c + dc, path + [(c, r)]))     # change appended path tuple orientation according to the requirement
                    visit.add((r + dr, c + dc))

        return []
    
    def get_all_access_points(self, list_of_products_to_collect):
        list_of_products_and_their_access_points = []
        for productID in list_of_products_to_collect:
            product_location = self.get_product_location(productID) #get product location
            product_location = (int(product_location[0]), int(product_location[1]))
            
            shelf_locations = [] 
            for _ , location in self.shelf_info.iterrows(): #find the access points for each product
                shelf_locations.append((location["xLocation"], location["yLocation"]))
            north_access_point = (product_location[0], product_location[1] + 1)
            south_access_point = (product_location[0], product_location[1] - 1)
            east_access_point =  (product_location[0] + 1 , product_location[1])
            west_access_point =  (product_location[0] - 1, product_location[1])
            
            all_access_points = [] #list containing all access points
            if(north_access_point not in shelf_locations and north_access_point[1] < self.max_y_index): all_access_points.append(north_access_point)
            if(south_access_point not in shelf_locations and south_access_point[1] > 0): all_access_points.append(south_access_point)
            if(east_access_point not in shelf_locations and east_access_point[0] < self.max_x_index):  all_access_points.append(east_access_point)
            if(west_access_point not in shelf_locations and west_access_point[0] > 0):  all_access_points.append(west_access_point)
            list_of_products_and_their_access_points.append((productID, all_access_points))
        return list_of_products_and_their_access_points # return list of products and their access points

    def get_shelves_containing_products(self, product_list):
        shelves_containing_products = [] 
        for productID in product_list:
            product_location = self.get_product_location(productID)
            shelf_location = (int(product_location[0]), int(product_location[1])) #shelf containg products
            shelves_containing_products.append(shelf_location)
        return shelves_containing_products
    
    #hill climbing starts
    # Function to find the neighbor route with the minimum distance
    def getBestRoute(self, tsp,neighbors):
        min_distance_route=neighbors[0]
        min_distance= self.distance(tsp,neighbors[0])
        # Iterate over the neighbors and update the minimum distance route
        for curr_route in neighbors:
            curr_route_distance= self.distance(tsp,curr_route)
            if curr_route_distance<min_distance:
                min_distance=curr_route_distance
                min_distance_route=curr_route
        return min_distance_route,min_distance

    def distance(self, tsp, curr_solution):
        cost=0
        for i in range(len(curr_solution)):
            cost+=float(tsp[curr_solution[i-1]][curr_solution[i]])

        return cost

    def randomSol(self, tsp):
        cities=list(range(len(tsp)))
        result=[]
        for i in range(len(tsp)):
            curr_city=cities[random.randint(0,len(cities)-1)]
            result.append(curr_city)
            cities.remove(curr_city)
        return result

    # Function to generate all possible neighbor
    def getneighbors(self, solution):
        neighbors=[]
        for i in range(len(solution)):
            for j in range(i+1, len(solution)):
                neighbor=solution.copy()
                neighbor[i]=solution[j]
                neighbor[j]=solution[i]
                neighbors.append(neighbor)
        return neighbors
    # Function implementing the hill climbing algorithm
    def hillclimbing(self, tsp, curr_route):
        curr_distance= self.distance(tsp,curr_route)
        # Generate the neighbor solutions
        neighbors= self.getneighbors(curr_route)
        # Find the best neighbor route
        min_distance_route,min_distance= self.getBestRoute(tsp,neighbors)
        # Continue iterating until no better solution is found
        while min_distance<curr_distance:
            curr_distance=min_distance
            curr_route=min_distance_route
            neighbors= self.getneighbors(curr_route)
            min_distance_route,min_distance= self.getBestRoute(tsp,neighbors)
        return curr_route

    #branch and bound starts
    def reduce_matrix(self, matrix):
        row_minimum_values = matrix.min(axis = 1).replace(float("INF"), 0) # find the minimum value for each row. If all values are infinity, set row min value to zero
        nodes = row_minimum_values.index.str[:-1].tolist()
        nodes = [*set(nodes)] #list of all the nodes without their access point. i,e. P1 will be in this list instead of P1N, P1S, etc.
        for node in nodes: #find minimum row value for each product. Examples, minimum of P1N, P1S, etc. will be minimum of product P1
            row_minimum_values.iloc[row_minimum_values.index.str.startswith(node)] = row_minimum_values.iloc[row_minimum_values.index.str.startswith(node)].min(axis = 0)
        reduced_matrix = matrix.sub(row_minimum_values, axis = 0) #substract minimum values from each row
        #repeat the same for columns
        col_minimum_values = reduced_matrix.min(axis = 0).replace(float("INF"), 0) 
        nodes = col_minimum_values.index.str[:-1].tolist()
        nodes = [*set(nodes)]
        for node in nodes:
            col_minimum_values.iloc[col_minimum_values.index.str.startswith(node)] = col_minimum_values.iloc[col_minimum_values.index.str.startswith(node)].min(axis = 0)
        reduced_matrix = reduced_matrix.sub(col_minimum_values, axis = 1) #substract minimum values from each column and get reduced matrix
        
        reduction_cost = row_minimum_values.sum() + col_minimum_values.sum() #add row and column minimum values to get cost of reduction
        return reduced_matrix, reduction_cost, row_minimum_values, col_minimum_values

    def get_unvisited_neighbours(self, matrix, visited_nodes):
        leaf_node = visited_nodes[-1]
        row = matrix.loc[leaf_node, :].values.flatten().tolist()
        col = matrix.columns
        neighbours = [col[index] for index, value in enumerate(row) if value < float("INF")] #neighbour are those values which are not infinity in the cost matrix. Store them in a list
        return neighbours #return list of unvisted neighbours

    def calculate_lower_bound(self, row_minimum_values, col_minimum_values):
        nodes = row_minimum_values.index.str[:-1].tolist()
        nodes = [*set(nodes)]
        lower_bound = 0
        for node in nodes: 
            lower_bound = lower_bound + row_minimum_values.iloc[row_minimum_values.index.str.startswith(node)].min(axis = 0) #for each product, take only minimum values and return the lower bound
            lower_bound = lower_bound + col_minimum_values.iloc[col_minimum_values.index.str.startswith(node)].min(axis = 0)
        return int(lower_bound)
        
    def Branch_N_Bound(self, matrix, access_point_array, parent_node):
        total_number_of_nodes = len(access_point_array)
        parent_matrix = matrix.copy()
        axis = parent_matrix.columns
        parent_matrix.drop("Dst", inplace = True) #drop destination node temporarily
        reduced_matrix, reduction_cost, row_minimum_values, col_minimum_values = self.reduce_matrix(parent_matrix) #reduce matrix
        lower_bound = self.calculate_lower_bound(row_minimum_values, col_minimum_values)
        destination_column = reduced_matrix.pop("Dst")
        myQueue = queue.PriorityQueue()
        visited = [axis[0]]
        myQueue.put((reduction_cost, -len(visited), visited, reduced_matrix)) #push it to queue
        while not myQueue.empty():
            matrix_cost, _, visited_nodes, reduced_matrix  = myQueue.get()
            if(len(visited_nodes) == total_number_of_nodes): break #if all nodes were visited and least cost was the matrix with all the nodes, then break out of the algorithm
            unvisited_neighbours = self.get_unvisited_neighbours(reduced_matrix, visited_nodes)
            dataframe_dictionary = {}
            current_node = visited_nodes[-1][0:2] 
            for neighbour in unvisited_neighbours: #visit each neighbour
                next_node = neighbour
                neighbour = neighbour[0:2]
                key = f"{current_node}_to_{neighbour}"
                if key not in dataframe_dictionary: #if matrix doesnt exisit, creat new matrix
                    BFS_matrix = reduced_matrix.copy()
                    BFS_matrix[BFS_matrix.index.str.startswith(current_node)] = BFS_matrix[BFS_matrix.index.str.startswith(current_node)].apply(lambda x: float("INF")) #make row infinity
                    BFS_matrix[[col for col in BFS_matrix if col.startswith(neighbour)]] = BFS_matrix[[col for col in BFS_matrix if col.startswith(neighbour)]].apply(lambda x: float("INF"))
                    for ancestor in visited_nodes:
                        BFS_matrix.loc[BFS_matrix.index.str.startswith(neighbour), BFS_matrix.columns.str.startswith(ancestor[0:2])] = float("INF")
                    BFS_matrix, reduction_cost, _, _ = self.reduce_matrix(BFS_matrix) #reduce matrix
                    dataframe_dictionary[key] = (BFS_matrix, reduction_cost) #add the matrix to the dictionary
                BFS_matrix, reduction_cost = dataframe_dictionary[key]
                overall_cost = matrix_cost + reduced_matrix.loc[visited_nodes[-1], next_node] + reduction_cost #calculate overall cost
                total_visited_nodes = visited_nodes + [next_node]
                if(len(total_visited_nodes) == total_number_of_nodes - 1):
                    BFS_matrix["Dst"] = destination_column
                myQueue.put((overall_cost, -len(total_visited_nodes), total_visited_nodes, BFS_matrix))
        return visited_nodes, matrix_cost, lower_bound # matrix_cost #return the nodes to be visited and the cost
    
    #NNF starts
    # input access point array and (current node, access point)
    # returns node index as per matrix
    def get_node_index(self, array, node):
        sum_y = 0
        for x, y in array:
            if x == node[0]:
                sum_y += node[1]
                break
            sum_y += y
        return sum_y

    # nearest neighbor algorithm 
    def nearest_neighbor(self, graph, access_points_array, source):
        # add initial node to tour with access point
        tour = [source]
        curr_cost = 0
        level = len(tour)
        # add initial node in visted
        nodes_visited = [source[0]]
        while level < len(access_points_array):
            parent_graph_index = self.get_node_index(access_points_array,tour[level-1])
            minimum = float('INF')
            # iterate over matrix based on access point array to find mininmum
            for i in range(len(access_points_array)):
                if i not in nodes_visited:
                    for j in range(access_points_array[i][1]):
                        node_index = self.get_node_index(access_points_array,(i,j))
                        if graph[parent_graph_index][node_index] < minimum and parent_graph_index != node_index:
                            minimum = graph[parent_graph_index][node_index]
                            access_point = j
                            node = i
            # minimum cost node and corresponding access point to visited
            nodes_visited.append(node)
            tour = tour + [(node,access_point)]
            level = len(tour)
            curr_cost = curr_cost + minimum
        # add destination to tour
        source_index = self.get_node_index(access_points_array,tour[-1])	
        dest_index = self.get_node_index(access_points_array,tour[0])	
        curr_cost = curr_cost + graph[source_index][dest_index]
        tour.append(tour[0])
        return tour, curr_cost

    # prim algorithm for getting lower bound
    def prim_MST(self, graph, access_points_array):
        source = random.randint(0, len(access_points_array)-1) # random node
        # add initial node to nodes visited
        nodes_visited = [source]
        curr_cost = 0
        minimum_route_cost = float('INF')
        # iterate over all directions to get minimum spanning tree
        for direction in range(access_points_array[source][1]):
            tour = [(source,direction)]
            while len(tour) < len(access_points_array): 
                minimum = float('INF')
                # iterate over matrix based on access point array to find mininmum
                for i in range(len(access_points_array)):
                    if i not in nodes_visited:
                        for j in range(access_points_array[i][1]):
                            node_index = self.get_node_index(access_points_array,(i,j))
                            for x,y in tour:
                                parent_node_index = self.get_node_index(access_points_array,(x,y))
                                if graph[parent_node_index][node_index] < minimum and parent_node_index != node_index:
                                    minimum = graph[parent_node_index][node_index]
                                    access_point = j
                                    node = i                        
                # check whether route is minimum
                nodes_visited.append(node)
                tour += [(node,access_point)]
                curr_cost = curr_cost + minimum
                if curr_cost > minimum_route_cost:
                    break
            # check direction wise minimum cost
            if curr_cost < minimum_route_cost:
                minimum_route_cost = curr_cost
                minimum_route_tour = tour

        return minimum_route_tour, minimum_route_cost
    
    def create_matrix(self, list_of_worker_product_and_drop_location):
        reverse_list_of_product_access_points_and_worker_and_drop_locations = [(item[0], [(product_location[1],product_location[0]) for product_location in item[1]]) for item in list_of_worker_product_and_drop_location]
        output_matrix = []
        path_from_src_to_dest = []
        for row_index, source in enumerate(reverse_list_of_product_access_points_and_worker_and_drop_locations):
            source_id = source[0]
            source_access_points = source[1]
            for source_access_point in source_access_points:
                curr_row = []
                temp_row = []
                for col_index, destination in enumerate(reverse_list_of_product_access_points_and_worker_and_drop_locations):
                    destination_id = destination[0]
                    destination_access_points = destination[1]
                    for destination_access_point in destination_access_points:
                        if(source_id == destination_id):
                            curr_row.append(float("INF"))
                            temp_row.append([])
                        else:
                            path = self.bfs_shortest_path(self.map, source_access_point, destination_access_point)
                            curr_row.append(len(path) - 1)
                            temp_row.append(path)
                            # path_from_src_to_dest.append([(source_location[1], source_location[0]), (destination_location[1], destination_location[0]), path])
                output_matrix.append(curr_row)
                path_from_src_to_dest.append(temp_row)
        return output_matrix, path_from_src_to_dest
    
    def BnB_create_matrix(self, list_of_worker_product_and_drop_location): #create matrix, same function as the above one, just that this returns a dataframe used for Branch-And-Bound
        reverse_list_of_product_access_points_and_worker_and_drop_locations = [(item[0], [(product_location[1],product_location[0]) for product_location in item[1]]) for item in list_of_worker_product_and_drop_location]
        axis = []
        for index, item in enumerate(list_of_worker_product_and_drop_location):
            if(item[0] == "W"): axis.append("W  ")
            elif(item[0] == "Dst"): axis.append("Dst")
            else:
                for access_point_location in item[1]:
                    item_location = self.get_product_location(item[0])
                    item_location = (int(item_location[0]), int(item_location[1]))
                    x_difference = item_location[0] - access_point_location[0]
                    y_difference = item_location[1] - access_point_location[1]
                    if(y_difference < 0): axis.append(f"P{index}N")
                    if(y_difference > 0): axis.append(f"P{index}S")
                    if(x_difference < 0): axis.append(f"P{index}E")
                    if(x_difference > 0): axis.append(f"P{index}W")
        output_matrix = []
        path_from_src_to_dest = []
        for row_index, source in enumerate(reverse_list_of_product_access_points_and_worker_and_drop_locations):
            source_id = source[0]
            source_access_points = source[1]
            for source_access_point in source_access_points:
                curr_row = []
                temp_row = []
                for col_index, destination in enumerate(reverse_list_of_product_access_points_and_worker_and_drop_locations):
                    destination_id = destination[0]
                    destination_access_points = destination[1]
                    for destination_access_point in destination_access_points:
                        if(source_id == destination_id):
                            curr_row.append(float("INF"))
                            temp_row.append([])
                        else:
                            path = self.bfs_shortest_path(self.map, source_access_point, destination_access_point)
                            curr_row.append(len(path) - 1)
                            temp_row.append(path)
                output_matrix.append(curr_row)
                path_from_src_to_dest.append(temp_row)
        matrix = pd.DataFrame(output_matrix, index = axis, columns = axis) #create dataframe
        path_matrix = pd.DataFrame(path_from_src_to_dest, index = axis, columns = axis) 
        return matrix, path_matrix
    
    def get_access_points_array(self, list_of_worker_product_and_drop_location): #get access points for all products
        access_points_array = []
        for index, ele in enumerate(list_of_worker_product_and_drop_location):
            num_of_access_points = len(ele[1])
            access_points_array.append((index, num_of_access_points))
        return access_points_array
    
    def print_weight_matrix(self, initial_matrix, access_points_array):
        axis = []
        for access_point in access_points_array:
            node = access_point[0]
            num_access_points = access_point[1]
            for i in range(num_access_points):
                if(node == 0): axis.append("W")
                elif(node == len(access_points_array) - 1): axis.append("Dst")
                else:
                    if(i == 0): axis.append("P" + str(node) + "N")
                    if(i == 1): axis.append("P" + str(node) + "S")
                    if(i == 2): axis.append("P" + str(node) + "E")
                    if(i == 3): axis.append("P" + str(node) + "W")
        df = pd.DataFrame(initial_matrix, index = axis, columns = axis)
        # with pd.option_context('display.max_rows', None, 'display.max_columns', None):  # more options can be specified also
        print("\n\n", df)
    
    @calculate_runtime
    def get_optimal_route(self, list_of_products_to_collect):
        algorithm_used = self.algorithm_selected
        lower_bound = None
        upper_bound = 0
        route_cost = 0
        list_of_all_product_locations = self.get_all_access_points(list_of_products_to_collect)
        list_of_worker_product_and_drop_location = [("W", [self.worker_location])] + list_of_all_product_locations + [("Dst", [self.drop_location])]
        final_route = []
        upper_bound_route = []
        try: #run the algorithm selected by the user
            if(self.algorithm_selected == "Brute Force: Branch And Bound for TSP"):
                initial_matrix, path_from_src_to_dest = self.BnB_create_matrix(list_of_worker_product_and_drop_location)
                access_points_array = self.get_access_points_array(list_of_worker_product_and_drop_location)
                random_starting_location = random.randint(0, len(access_points_array) -1)
                order_of_nodes_to_traverse, cost, lower_bound = self.Branch_N_Bound(initial_matrix, access_points_array, random_starting_location)
                for src_node, dest_node in zip(order_of_nodes_to_traverse, order_of_nodes_to_traverse[1:]):
                    final_route.append(path_from_src_to_dest.at[src_node, dest_node])
                    route_cost = route_cost + len(final_route[-1])
                route_cost = route_cost - len(order_of_nodes_to_traverse)
            elif(self.algorithm_selected == "Custom: Hill Climbing Algorithm for TSP"):
                list_of_worker_product_and_drop_location_single_access = []
                for index, product_or_worker in enumerate(list_of_worker_product_and_drop_location):
                    node = product_or_worker[0]
                    access_point = [product_or_worker[1][0]]
                    list_of_worker_product_and_drop_location_single_access.append((node, access_point))
                initial_matrix, path_from_src_to_dest = self.create_matrix(list_of_worker_product_and_drop_location_single_access[:-1])
                curr_route = [i for i in range(len(list_of_worker_product_and_drop_location[:-1]))]
                order_of_nodes_to_traverse = self.hillclimbing(initial_matrix, curr_route)
                rotation_index = order_of_nodes_to_traverse.index(0)
                order_of_nodes_to_traverse = order_of_nodes_to_traverse[rotation_index:] + order_of_nodes_to_traverse[:rotation_index]
                for src, dest in zip(order_of_nodes_to_traverse, order_of_nodes_to_traverse[1:]):
                    path = path_from_src_to_dest[src][dest]
                    final_route.append(path)
                    route_cost = route_cost + len(final_route[-1])
                last_product_location = final_route[-1][-1]
                reverse_last_product_location = (last_product_location[1], last_product_location[0])
                reverse_drop_location = (self.drop_location[1], self.drop_location[0])
                last_product_to_drop_location_path = self.bfs_shortest_path(self.map, reverse_last_product_location, reverse_drop_location)
                final_route.append(last_product_to_drop_location_path)
                route_cost = route_cost + len(final_route[-1])
                route_cost = route_cost - len(order_of_nodes_to_traverse) + 1
            elif(self.algorithm_selected == "Nearest Neighbor First for TSP"):
                    initial_matrix, path_from_src_to_dest = self.create_matrix(list_of_worker_product_and_drop_location)
                    temp_array = self.get_access_points_array(list_of_worker_product_and_drop_location)
                    access_points_array = temp_array[:-1]
                    minimum_route = []
                    minimum_tot_dist = float('INF')
                    for i in range(len(access_points_array)):
                        for j in range(access_points_array[i][1]):
                            route, distance = self.nearest_neighbor(initial_matrix,access_points_array,(i,j))
                            if distance < minimum_tot_dist:
                                minimum_route = route
                                minimum_tot_dist = distance
                    order_of_nodes_to_traverse = minimum_route[:-1]
                    for rotation_index, node in enumerate(order_of_nodes_to_traverse):
                        if(node[0] == 0):
                            break
                    order_of_nodes_to_traverse = order_of_nodes_to_traverse[rotation_index:] + order_of_nodes_to_traverse[:rotation_index]
                    order_of_nodes_to_traverse.append((temp_array[-1][0],0))
                    for src_node, dest_node in zip(order_of_nodes_to_traverse, order_of_nodes_to_traverse[1:]):
                        row_number = 0
                        col_number = 0
                        for node in access_points_array:
                            if(src_node[0] == node[0]): break
                            else: row_number = row_number + node[1]
                        row_number = row_number + src_node[1]
                        for node in access_points_array:
                            if(dest_node[0] == node[0]): break
                            else: col_number = col_number + node[1]
                        col_number = col_number + dest_node[1]
                        final_route.append(path_from_src_to_dest[row_number][col_number])
                        route_cost = route_cost + len(final_route[-1])
                    if(self.worker_location != self.drop_location):
                        route_cost = route_cost - len(final_route[-1])
                        last_product_location = final_route.pop()[0]
                        reverse_last_product_location = (last_product_location[1], last_product_location[0])
                        reverse_drop_location = (self.drop_location[1], self.drop_location[0])
                        last_product_to_drop_location_path = self.bfs_shortest_path(self.map, reverse_last_product_location, reverse_drop_location)
                        final_route.append(last_product_to_drop_location_path)
                        route_cost = route_cost + len(final_route[-1])
                    route_cost = route_cost - len(order_of_nodes_to_traverse) + 1
        except:
            # implement nearest neighbor if timeout
            order_of_nodes_to_traverse = []
            initial_matrix, path_from_src_to_dest = self.create_matrix(list_of_worker_product_and_drop_location)
            temp_array = self.get_access_points_array(list_of_worker_product_and_drop_location)
            access_points_array = temp_array[:-1]
            minimum_route = []
            minimum_tot_dist = float('INF')
            for i in range(len(access_points_array)):
                for j in range(access_points_array[i][1]):
                    route, distance = self.nearest_neighbor(initial_matrix,access_points_array,(i,j))
                    if distance < minimum_tot_dist:
                        minimum_route = route
                        minimum_tot_dist = distance
            order_of_nodes_to_traverse = minimum_route[:-1]
            for rotation_index, node in enumerate(order_of_nodes_to_traverse):
                if(node[0] == 0):
                    break
            order_of_nodes_to_traverse = order_of_nodes_to_traverse[rotation_index:] + order_of_nodes_to_traverse[:rotation_index]
            order_of_nodes_to_traverse.append((temp_array[-1][0],0))
            
            for src_node, dest_node in zip(order_of_nodes_to_traverse, order_of_nodes_to_traverse[1:]):
                row_number = 0
                col_number = 0
                for node in access_points_array:
                    if(src_node[0] == node[0]): break
                    else: row_number = row_number + node[1]
                row_number = row_number + src_node[1]
                for node in access_points_array:
                    if(dest_node[0] == node[0]): break
                    else: col_number = col_number + node[1]
                col_number = col_number + dest_node[1]
                final_route.append(path_from_src_to_dest[row_number][col_number])
                route_cost = route_cost + len(final_route[-1])
            if(self.worker_location != self.drop_location):
                route_cost = route_cost - len(final_route[-1])
                last_product_location = final_route.pop()[0]
                reverse_last_product_location = (last_product_location[1], last_product_location[0])
                reverse_drop_location = (self.drop_location[1], self.drop_location[0])
                last_product_to_drop_location_path = self.bfs_shortest_path(self.map, reverse_last_product_location, reverse_drop_location)
                final_route.append(last_product_to_drop_location_path)
                route_cost = route_cost + len(final_route[-1])
            route_cost = route_cost - len(order_of_nodes_to_traverse) + 1
            algorithm_used = "Nearest Neighbor First for TSP"

        order_of_nodes_to_traverse = []
        for index, product_or_worker_or_drop_location in enumerate(list_of_worker_product_and_drop_location):
            access_point = (product_or_worker_or_drop_location[1][0][1], product_or_worker_or_drop_location[1][0][0])
            order_of_nodes_to_traverse.append(access_point)
        for src, dest in zip(order_of_nodes_to_traverse, order_of_nodes_to_traverse[1:]):
            path = self.bfs_shortest_path(self.map, src, dest)
            upper_bound = upper_bound + len(path)
            upper_bound_route.append(path)
        upper_bound = upper_bound - len(order_of_nodes_to_traverse) + 1
        if(route_cost > upper_bound):
            final_route = upper_bound_route
            algorithm_used = "Returning the route as per the input order list"
        return final_route, algorithm_used, lower_bound, upper_bound
    
class Interface:
    warehouse = None
    input_product_list = None
    input_product_list_filename = None
    products_to_collect = None
    #color variables
    red_text = "\033[91m"
    green_text = "\033[32m"
    cyan_text = "\033[36m"
    yellow_text = "\033[33m"
    pink_text = "\033[95m"
    color_reset = "\033[0m"
    
    def __init__(self, Warehouse):
        self.warehouse = Warehouse

    def my_print(self, input_string):
        if(self.warehouse.export_to_file == "Enabled"):
            output_file = open("instructions_to_collect_products.txt", "a")
            output_file.write(input_string)
            output_file.write("\n")
        if(input_string.strip().startswith("[DEBUG MODE]")): pass #self.color_print(input_string, "red")
        else: self.color_print(input_string, "green")
    
    def color_print(self, input_string, color):
        #color variables
        red_text = "\033[91m"
        green_text = "\033[32m"
        cyan_text = "\033[36m"
        yellow_text = "\033[33m"
        pink_text = "\033[95m"
        color_reset = "\033[0m"
        if(color == "yellow"): print(f"{yellow_text}{input_string}{color_reset}")
        elif(color == "green"): print(f"{green_text}{input_string}{color_reset}")
        elif(color == "cyan"): print(f"{cyan_text}{input_string}{color_reset}")
        elif(color == "red"): print(f"{red_text}{input_string}{color_reset}")
        elif(color == "pink"): print(f"{pink_text}{input_string}{color_reset}")
             
    def print_instructions(self, path, products_to_collect):
        print_instruction_count = 1
        self.my_print(f"\n\n{self.pink_text}************ {self.yellow_text}Directions To Collect Product List: {self.cyan_text}{products_to_collect}  {self.pink_text}********************{self.color_reset}\n\n")
        if(self.warehouse.debug_mode == "Enabled"):
            complete_path = []
            for sub_path in path:
                complete_path = complete_path + sub_path
            self.my_print(f"[DEBUG MODE]: Path to get to the product: {complete_path}\n\n")

        dir_and_number_of_steps = []
        for index, sub_path in enumerate(path):
            if(len(sub_path) <= 1):
                self.my_print(f"{print_instruction_count}. Pick product: {products_to_collect[index]}")
                print_instruction_count = print_instruction_count + 1
                continue
            traversal_order = []
            sub_path.append(sub_path[-1])
            for current_location, next_location in zip(sub_path, sub_path[1:]):
                if(current_location[1] < next_location[1]):
                    traversal_order.append("north")
                elif(current_location[1] > next_location[1]):
                    traversal_order.append("south")
                elif(current_location[0] < next_location[0]):
                    traversal_order.append("east")
                elif(current_location[0] > next_location[0]):
                    traversal_order.append("west")
            number_of_steps = [(sum(1 for _ in group), dir) for dir, group in itertools.groupby(traversal_order)]
            dir_and_number_of_steps.append(number_of_steps)
            starting_location = sub_path[0]
            for step_count, dir in number_of_steps:
                if(dir == "north"): ending_location = (starting_location[0], starting_location[1] + step_count)
                if(dir == "south"): ending_location = (starting_location[0], starting_location[1] - step_count)
                if(dir == "east"): ending_location = (starting_location[0] + step_count, starting_location[1])
                if(dir == "west"): ending_location = (starting_location[0] - step_count, starting_location[1])
                self.my_print(f"{print_instruction_count}. Move {dir} {step_count} steps from location {starting_location} to location {ending_location}.")
                print_instruction_count = print_instruction_count + 1
                starting_location = ending_location
            if(index == len(path) - 1): continue
            self.my_print(f"{print_instruction_count}. Pick product: {products_to_collect[index]}")
            print_instruction_count = print_instruction_count + 1
        self.my_print(f"{print_instruction_count}. Done collecting all the products!")
        if(self.warehouse.debug_mode == "Enabled"):
            self.my_print(f"\n\n[DEBUG MODE]: Number of products in the warehouse: {len(self.warehouse.product_data)}")
            self.my_print(f"[DEBUG MODE]: Number of shelves in the warehouse: {len(self.warehouse.shelf_info)}")
        return dir_and_number_of_steps
                        
    def show_map(self, dir_and_number_of_steps, list_of_shelves_containing_products):
        #worker, shelf and empty space representation
        shelf_representation = "\u2588" #"\u25A0"  "\u2588"
        worker_representation = "\U0001F60A" #Smiley: "\U0001F60A" smaller smiley: "\u263A"
        drop_location_representation = "\U0001F44D" #Smiley: "\U0001F60A" smaller smiley: "\u263A"
        empty_space_representation = "_"
        
        #box variables to dwar a wall around the warehouse
        box_top_left_representation = "\u250C\u2500\u2500"
        box_bottom_left_representation = "\u2514\u2500\u2500"
        box_top_right_representation = "\u2500\u2500\u2510"
        box_bottom_right_representation = "\u2500\u2500\u2518"
        box_horizontal_line_representation = "\u2500\u2500\u2500"
        box_vertical_line_representation = "\u2502"
        
        #Arrow Representation
        up_arrow_representation    = "\u2191"
        down_arrow_representation  = "\u2193"
        left_arrow_representation  = "\u2190"
        right_arrow_representation = "\u2192" #\u2192 \u0362
        left_right_arrow_representation = " \u2190\u0362 " #\u2192 \u0362
        up_down_arrow_representation = "\u2191 \u2193"
        
        #color variables
        red_text = "\033[91m"
        green_text = "\033[32m"
        cyan_text = "\033[36m"
        yellow_text = "\033[33m"
        pink_text = "\033[95m"
        color_reset = "\033[0m"
        
        spacing = 3 #spacing between the shelves
        
        shelf_locations = []
        for productID, location in self.warehouse.shelf_info.iterrows():
            shelf_locations.append((location["xLocation"], location["yLocation"]))
        
        up_arrow_list = []    
        down_arrow_list = []    
        left_arrow_list = []    
        right_arrow_list = []
        starting_location = self.warehouse.worker_location
        current_location = starting_location
        locations_traversed = [current_location]
        list_of_all_access_points = []
        total_step_count = 0
        for step_count_dir in dir_and_number_of_steps:
            for num_steps_direction in step_count_dir:
                step_count = num_steps_direction[0]
                direction = num_steps_direction[1]
                total_step_count = total_step_count + step_count
                for _ in range(step_count):
                    if(direction == "north"):
                        up_arrow_list.append(current_location)
                        current_location = (current_location[0], current_location[1] + 1)
                    if(direction == "south"):
                        down_arrow_list.append(current_location)
                        current_location = (current_location[0], current_location[1] - 1)
                    if(direction == "east"):
                        right_arrow_list.append(current_location)
                        current_location = (current_location[0] + 1, current_location[1])
                    if(direction == "west"):
                        left_arrow_list.append(current_location)
                        current_location = (current_location[0] - 1, current_location[1])
                locations_traversed.append(current_location)
            list_of_all_access_points.append(current_location)
        up_down_arrow_list = list(set(up_arrow_list).intersection(down_arrow_list))
        left_right_arrow_list = list(set(left_arrow_list).intersection(right_arrow_list))
                
        print(f"\n\n{pink_text}************\t{yellow_text}Warehouse Map\t{pink_text}********************{color_reset}\n\n")
        print(f"{red_text}Legends:{color_reset}") #Print the legend
        print(f"{green_text}{empty_space_representation: ^{spacing}}{color_reset}", end="")
        print("- Empty Spaces\n")
        print(f"{cyan_text}{shelf_representation: ^{spacing}}{color_reset}", end="")
        print("- Shelf\n")
        print(f"{worker_representation: ^{2}}", end="")
        print("- Worker\n")
        print(f"{drop_location_representation: ^{2}}", end="")
        print("- Drop Location\n")
        print(f"{yellow_text}{up_arrow_representation} {down_arrow_representation} {left_arrow_representation} {right_arrow_representation}{color_reset} - Direction for the worker\n")
        print(f"{pink_text}{up_arrow_representation} {down_arrow_representation} {left_arrow_representation} {right_arrow_representation}{color_reset} - Access Point\n")
        print(f"{pink_text}{shelf_representation: ^{spacing}}{color_reset} - Shelf containing product\n")
        print(f"{red_text}    N  ")
        print("  W + E")
        print(f"    S  {color_reset}")
        print()
        
        print()
        
        #print the map of the warehouse
        for y_index in range(self.warehouse.max_y_index, -3, -1):   
            for x_index in range(-2, self.warehouse.max_x_index + 1): 
                if( x_index == -2 ): #print the y-axis
                    if(y_index >=0 and y_index < self.warehouse.max_y_index):  print(f"{red_text}{y_index: ^{spacing}}{color_reset}", end="")
                    else: print(f"{' ': ^{spacing}}", end="")
                elif( x_index == -1 ): #daw left wall of the warehouse
                    if(y_index == self.warehouse.max_y_index):  print(f"{box_top_left_representation: ^{spacing}}", end="")
                    elif(y_index == -1):  print(f"{box_bottom_left_representation: ^{spacing}}", end="")
                    elif(y_index == -2):  print(f"{' ': ^{spacing}}", end="")
                    else: print(f"{box_vertical_line_representation: <{spacing}}", end="")
                elif( x_index == self.warehouse.max_x_index ): #draw right wall of the warehouse
                    if(y_index == self.warehouse.max_y_index):  print(f"{box_top_right_representation: ^{spacing}}", end="")
                    elif(y_index == -1):  print(f"{box_bottom_right_representation: ^{spacing}}", end="")
                    elif(y_index == -2):  print(f"{' ': ^{spacing}}", end="")
                    else: print(f"{box_vertical_line_representation: >{spacing}}", end="")
                elif( y_index == -1 or y_index == self.warehouse.max_y_index): #draw South side Wall of the warehouse
                    if(x_index >=0 and x_index < self.warehouse.max_x_index):  print(f"{box_horizontal_line_representation: ^{spacing}}", end="") #draw South side Wall of the warehouse
                elif( y_index == -2 ): #draw x-axis
                    if(x_index >=0 and x_index < self.warehouse.max_x_index):  print(f"{red_text}{x_index: ^{spacing}}{color_reset}", end="")
                    else: print(f"{' ': ^{spacing}}", end="")
                else: #Draw the worker and the shelves and the directions
                    if((x_index, y_index) in list_of_all_access_points):    arrow_color = pink_text
                    else: arrow_color = yellow_text
                    if ((x_index, y_index) in list_of_shelves_containing_products):
                        print(f"{pink_text}{shelf_representation: ^{spacing}}{color_reset}", end="")
                    elif ((x_index, y_index) in shelf_locations):
                        print(f"{cyan_text}{shelf_representation: ^{spacing}}{color_reset}", end="")
                    elif ((x_index, y_index) == self.warehouse.worker_location):
                        print(f"{worker_representation: ^{2}}", end="")
                    elif ((x_index, y_index) == self.warehouse.drop_location):
                        print(f"{drop_location_representation: ^{2}}", end="")
                    elif ((x_index, y_index) in up_down_arrow_list):
                        print(f"{arrow_color}{up_down_arrow_representation: ^{spacing}}{color_reset}", end="")
                    elif ((x_index, y_index) in left_right_arrow_list):
                        print(f"{arrow_color}{left_right_arrow_representation: ^{spacing}}{color_reset}", end="")
                    elif ((x_index, y_index) in up_arrow_list):
                        print(f"{arrow_color}{up_arrow_representation: ^{spacing}}{color_reset}", end="")
                    elif ((x_index, y_index) in down_arrow_list):
                        print(f"{arrow_color}{down_arrow_representation: ^{spacing}}{color_reset}", end="")
                    elif ((x_index, y_index) in left_arrow_list):
                        print(f"{arrow_color}{left_arrow_representation: ^{spacing}}{color_reset}", end="")
                    elif ((x_index, y_index) in right_arrow_list):
                        print(f"{arrow_color}{right_arrow_representation: ^{spacing}}{color_reset}", end="")
                    else:
                        print(f"{green_text}{empty_space_representation: ^{spacing}}{color_reset}", end="")        
            print("\n")
        
        print(f"Locations traversed: ", end="")
        for location in locations_traversed[:-1]:
            print(f"{location} -> ", end="")
        print(locations_traversed[-1])
        
        return total_step_count

    def print_statistics(self, total_step_count, algorithm_used, runtime, lower_bound, upper_bound): 
        if(algorithm_used == self.warehouse.algorithm_selected): print(f"\n{self.cyan_text}Algorithm used:         {self.green_text}    {self.warehouse.algorithm_selected}{self.color_reset}")
        else: 
            if(algorithm_used == "Nearest Neighbor First for TSP"): 
                print(f"\n{self.cyan_text}Algorithm used:         {self.green_text}    {algorithm_used}{self.yellow_text} instead of {self.red_text}{self.warehouse.algorithm_selected}{self.yellow_text} because of Timeout.{self.color_reset}")
            else:
                print(f"\n{self.cyan_text}Algorithm used:         {self.green_text}    {algorithm_used}{self.yellow_text} instead of {self.red_text}{self.warehouse.algorithm_selected}{self.yellow_text} because input order list (upper bound) is better than algorithm's output.")
        print(f"{self.cyan_text}Total Execution Time:       {self.green_text}{runtime} seconds{self.color_reset}")
        print(f"{self.cyan_text}Total Number of Steps:      {self.green_text}{total_step_count} steps{self.color_reset}")
        
        # Debug Mode MST output
        if(self.warehouse.debug_mode == "Enabled"):
            if(algorithm_used == "Brute Force: Branch And Bound for TSP"):
                print(f"\n\n{self.red_text}[DEBUG MODE] Upper bound: {upper_bound} - Derrived from cost of input order list.")
                print(f"[DEBUG MODE] Lower bound: {lower_bound} - Derived from the cost of reduction of initial cost matrix.{self.color_reset}")
            elif(algorithm_used == "Nearest Neighbor First for TSP"):
                list_of_all_product_locations = self.warehouse.get_all_access_points(self.products_to_collect)
                list_of_worker_product_and_drop_location = [("W", [self.warehouse.worker_location])] + list_of_all_product_locations + [("Dst", [self.warehouse.drop_location])]
                graph, path = self.warehouse.create_matrix(list_of_worker_product_and_drop_location)
                temp_array = self.warehouse.get_access_points_array(list_of_worker_product_and_drop_location)
                access_points_array = temp_array[:-1]
                route, cost = self.warehouse.prim_MST(graph,access_points_array)
                print(f"\n\n{self.red_text}[DEBUG MODE] MST Graph Nodes: {route}")
                print(f"\n[DEBUG MODE] Upper Bound: {upper_bound} - Derrived from cost of input order list.")
                print(f"[DEBUG MODE] Lower Bound: {cost} - Derived from the cost of Minimum Spanning Tree.{self.color_reset}")
    
    def execute_user_input(self, user_input, menu):
        if(menu == "main"):
            if(user_input == "1"): #Run the "Collect a product!" input
                while(True):
                    try:    
                        self.color_print(f"\n1. Get list of products from the input file: {self.input_product_list_filename}", "yellow")
                        self.color_print(f"2. Manually input a list of products", "yellow")
                        user_input = input("\nEnter your choice from the above options. Enter a number from 1 to 2.\n> ")
                        if(user_input == "1"):
                            if(len(self.input_product_list) < 10):   self.color_print("\nFollowing orders are available in the file:\n", "yellow")
                            else: self.color_print(f"\nThe input file has {len(self.input_product_list)} orders. Displaying top 10 of them. To select an order beyond 10, enter the line number of the order as it appears in the input file.\n", "yellow")
                            for index, product in enumerate(self.input_product_list):
                                self.color_print(f"{index + 1}. {product}", "cyan")
                                if(index == 9): break
                            while(True):
                                try:
                                    user_input = input(f"\nSelect the test case you want to run. Enter your choice from 1 through {len(self.input_product_list)}.\n> ")
                                    if(int(user_input) < 1): raise Exception
                                    self.products_to_collect = self.input_product_list[int(user_input) - 1]
                                    self.color_print(f"\nOrder List Selected: {self.products_to_collect}", "green")
                                    break
                                except:
                                    self.color_print(f"\nInvalid input! Please input a number from 1 through {len(self.input_product_list)}.", "red")
                            while(True):    
                                try:
                                    self.color_print(f"\nCurrent Worker Location: {self.warehouse.worker_location}", "yellow")
                                    user_input = input("Press enter key if you do not want to change the worker's location.\nTo change worker's location, enter the worker's new location. Input Format: If you want to update the worker's location to (1,2) then enter 1,2 as input below. \n> ") 
                                    if(user_input == ""): 
                                        self.color_print(f"\nThe worker location is set to: {self.warehouse.worker_location}", "green")
                                        break
                                    worker_initial_location = user_input.split(",")
                                    worker_initial_location = (int(worker_initial_location[0]), int(worker_initial_location[1]))
                                    shelf_locations = []
                                    for productID, location in self.warehouse.shelf_info.iterrows():
                                        shelf_locations.append((location["xLocation"], location["yLocation"]))
                                    if(worker_initial_location[0] >= 0 and worker_initial_location[0] < self.warehouse.max_x_index and worker_initial_location[1] >= 0 and worker_initial_location[1] < self.warehouse.max_y_index):
                                        if(worker_initial_location not in shelf_locations):
                                            self.warehouse.worker_location = worker_initial_location #set the worker's location in the warehouse
                                            self.color_print(f"\nThe worker location is set to: {self.warehouse.worker_location}", "green")
                                            break
                                        else:
                                            self.color_print(f"\nInvalid Input. The worker's location can't be where a shelf is located. Please try again!\n", "red")
                                            continue
                                    else:
                                        self.color_print(f"\nInput Out of Bounds. Enter input between (0,0) and ({self.warehouse.max_x_index - 1, self.warehouse.max_y_index - 1}). Please try again!\n", "red")
                                        continue
                                except: self.color_print(f"\nInvalid input. Please try again!", "red")
                            while(True):
                                try:    
                                    self.color_print(f"\nCurrent Drop Location:{self.warehouse.drop_location}", "yellow")
                                    user_input = input("Press enter key if you do not want to change the drop location.\nTo change drop location, enter the final drop location of the products. Input Format: If you want to update the drop location to (1,2) then enter 1,2 as input below. \n> ")
                                    if(user_input == ""): 
                                        self.color_print(f"\nThe drop location is set to: {self.warehouse.drop_location}", "green")
                                        break
                                    drop_location = user_input.split(",")
                                    drop_location = (int(drop_location[0]), int(drop_location[1]))
                                    shelf_locations = []
                                    for productID, location in self.warehouse.shelf_info.iterrows():
                                        shelf_locations.append((location["xLocation"], location["yLocation"]))
                                    if(drop_location[0] >= 0 and drop_location[0] < self.warehouse.max_x_index and drop_location[1] >= 0 and drop_location[1] < self.warehouse.max_y_index):
                                        if(drop_location not in shelf_locations):
                                            self.warehouse.drop_location = drop_location #set the drop location in the warehouse
                                            self.color_print(f"\nThe drop location is set to: {self.warehouse.drop_location}", "green")
                                            break
                                        else:
                                            self.color_print(f"\nInvalid Input. The drop location can't be where a shelf is located\n", "red")
                                            continue
                                    else:
                                        self.color_print(f"\nInput Out of Bounds. Enter input between (0,0) and (39,20)\n", "red")
                                        continue
                                except: self.color_print(f"\nInvalid input. Please try again!", "red")
                        elif(user_input == "2"):
                            while(True):
                                try:
                                    user_input = input("\nEnter the product IDs of the products you want to collect. Separate the IDs with a comma. For example, to collect products 45 and 149, input: 45, 149 \n> ")
                                    self.products_to_collect = [ int(x.strip()) for x in user_input.split(",")]
                                    for product in self.products_to_collect:
                                        _ = self.warehouse.get_product_location(product)
                                    while(True):    
                                        try:
                                            self.color_print(f"\nCurrent Worker Location: {self.warehouse.worker_location}", "yellow")
                                            user_input = input("Enter the location of the worker. Input Format: If you want to update the worker's location to (1,2) then enter 1,2 as input below. \n> ") 
                                            if(user_input == ""): 
                                                self.color_print(f"\nThe worker location is set to: {self.warehouse.worker_location}", "green")
                                                break
                                            worker_initial_location = user_input.split(",")
                                            worker_initial_location = (int(worker_initial_location[0]), int(worker_initial_location[1]))
                                            shelf_locations = []
                                            for productID, location in self.warehouse.shelf_info.iterrows():
                                                shelf_locations.append((location["xLocation"], location["yLocation"]))
                                            if(worker_initial_location[0] >= 0 and worker_initial_location[0] < self.warehouse.max_x_index and worker_initial_location[1] >= 0 and worker_initial_location[1] < self.warehouse.max_y_index):
                                                if(worker_initial_location not in shelf_locations):
                                                    self.warehouse.worker_location = worker_initial_location #set the worker's location in the warehouse
                                                    self.color_print(f"\nThe worker location is set to: {self.warehouse.worker_location}", "green")
                                                    break
                                                else:
                                                    self.color_print(f"\nInvalid Input. The worker's location can't be where a shelf is located. Please try again!\n", "red")
                                                    continue
                                            else:
                                                self.color_print(f"\nInput Out of Bounds. Enter input between (0,0) and ({self.warehouse.max_x_index - 1, self.warehouse.max_y_index - 1}). Please try again!\n", "red")
                                                continue
                                        except: self.color_print(f"\nInvalid input. Please try again!", "red")
                                    while(True):
                                        try:    
                                            self.color_print(f"\nCurrent Drop Location:{self.warehouse.drop_location}", "yellow")
                                            user_input = input("Enter the final drop location of the products. Input Format: If you want to update the drop location to (1,2) then enter 1,2 as input below. \n> ")
                                            if(user_input == ""): 
                                                self.color_print(f"\nThe drop location is set to: {self.warehouse.drop_location}", "green")
                                                break
                                            drop_location = user_input.split(",")
                                            drop_location = (int(drop_location[0]), int(drop_location[1]))
                                            shelf_locations = []
                                            for productID, location in self.warehouse.shelf_info.iterrows():
                                                shelf_locations.append((location["xLocation"], location["yLocation"]))
                                            if(drop_location[0] >= 0 and drop_location[0] < self.warehouse.max_x_index and drop_location[1] >= 0 and drop_location[1] < self.warehouse.max_y_index):
                                                if(drop_location not in shelf_locations):
                                                    self.warehouse.drop_location = drop_location #set the drop location in the warehouse
                                                    self.color_print(f"\nThe drop location is set to: {self.warehouse.drop_location}", "green")
                                                    break
                                                else:
                                                    self.color_print(f"\nInvalid Input. The drop location can't be where a shelf is located\n", "red")
                                                    continue
                                            else:
                                                self.color_print(f"\nInput Out of Bounds. Enter input between (0,0) and (39,20)\n", "red")
                                                continue
                                        except: self.color_print(f"\nInvalid input. Please try again!", "red")
                                    break
                                except:
                                    self.color_print("Invalid Input. Please try again!", "red")
                        else:   raise Exception
                    except: 
                        self.color_print("\nInvalid input. Please try again!", "red")
                        continue
                    (path, algorithm_used, lower_bound, upper_bound), runtime = self.warehouse.get_optimal_route(self.products_to_collect) #get path to the product
                    dir_and_number_of_steps = self.print_instructions(path, self.products_to_collect) #print the instruction to get the product and return back
                    list_of_shelves_containing_products = self.warehouse.get_shelves_containing_products(self.products_to_collect)
                    total_step_count = self.show_map(dir_and_number_of_steps, list_of_shelves_containing_products)
                    self.print_statistics(total_step_count, algorithm_used, runtime, lower_bound, upper_bound)
                    break
            elif(user_input == "2"): #Display location of a product
                while(True):
                    try:
                        product_ID = input(f"\nEnter the ID of the product to be located \n> ")
                        product_ID = int(product_ID)
                        product_location = self.warehouse.get_product_location(product_ID) #get product location
                        self.color_print(f"\nThe product {product_ID} is located at {product_location}", "green")
                        break
                    except: self.color_print("Invalid product. Please enter the ID of the product again!", "red")
            elif(user_input == "3"): #Enter settings menu
                self.display_settings_menu()
            elif(user_input == "4"): # Exit Program
                self.color_print("Exiting Program... Thank you!", "pink")
                sys.exit()
            else:
                self.color_print("Invalid option selected. Please try any option from the ones above!", "red")
                return
        elif(menu == "settings"):
            if(user_input == "1"): #Toggle debug mode
                if(self.warehouse.debug_mode == "Enabled"):
                    self.warehouse.debug_mode = "Disabled"
                else:
                    self.warehouse.debug_mode = "Enabled"
                self.color_print(f"\nThe debug mode is set to: {self.warehouse.debug_mode}", "green")
            elif(user_input == "2"): #Toggle export file mode
                if(self.warehouse.export_to_file == "Enabled"):
                    self.warehouse.export_to_file = "Disabled"
                else:
                    self.warehouse.export_to_file = "Enabled"
                self.color_print(f"\nThe export file mode is set to: {self.warehouse.export_to_file}", "green")
            elif(user_input == "3"): #Change the algorithm
                try:
                    self.color_print(f"\n\nChoose an algorithm from the options listed below.", "yellow")
                    for index, algorithm in enumerate(self.warehouse.algorithms_available):
                        self.color_print(f"{index + 1}: {algorithm}", "yellow")
                    user_input = input(f"\nSelect the algorithm. Please enter input from 1 to {len(self.warehouse.algorithms_available)} \n> ")
                    self.warehouse.algorithm_selected = self.warehouse.algorithms_available[int(user_input) - 1]
                    self.color_print(f"\nAlgorithm to solve TSP is set to: {self.warehouse.algorithm_selected}", "green")
                except:
                    self.color_print("Invalid Input. The algorithm was **NOT** set. Returning back to previous menu!", "red")
            elif(user_input == "4"): #Change product's drop location
                user_input = input("\nEnter the timeout duration (in seconds) upto which algorithm can run. Input Format: To set timeout interval to 30 seconds, enter 30 below. \n> ")
                try:
                    self.warehouse.timeout_interval = int(user_input)
                    self.color_print(f"\nTimeout duration was set to {self.warehouse.timeout_interval} seconds.", "green")
                except:
                    self.color_print("Invalid input! Timeout duration was **NOT** set. Returning back to the previous menu!", "red")
            elif(user_input =="5"): #Return to main menu
                return 1
            else:
                self.color_print("Invalid option selected. Please try any option from the ones above!", "red")

    def display_settings_menu(self):
        while(True):
            settings_menu_items = [
                                    f"1. Toggle debug mode. Current debug mode is set to: {self.warehouse.debug_mode}",
                                    f"2. Toggle export instruction mode. Current exportmode is set to: {self.warehouse.export_to_file}",
                                    f"3. Change the algorithm for calulating route. Current algorithm is set to: {self.warehouse.algorithm_selected}",
                                    f"4. Change the timeout of the algorithm. Currently the timeout is set to: {self.warehouse.timeout_interval} seconds",
                                    f"5. Return back to main menu",
                                ]
            ###Print Settings Menu
            print(f"{self.yellow_text}\n\n================================")
            print("          ** Settings Menu **\n")
            for menu_item in settings_menu_items: #print settings menu items
                print(f"{menu_item}")
            print(f"================================{self.color_reset}")
            user_input = input(f"\nInput your choice from the options above. Enter a choice 1 through {len(settings_menu_items)} \n> ")
            done_execution = self.execute_user_input(user_input, "settings") #execute the user input
            if(done_execution == 1): #return back to main menu if user is done changing settings
                return
        
    def display_main_menu(self):
        main_menu_items = [
                            "1. Collect a product!",
                            "2. Get location of a product!",
                            "3. Settings",
                            "4. Exit",
                        ]
        ###Print Main Menu
        print(f"{self.yellow_text}\n\n================================")
        print(f"          ** Main Menu **\n")
        for menu_item in main_menu_items: #Print main menu items
            print(f"{menu_item}")
        print(f"================================{self.color_reset}")
        user_input = input(f"\nInput your choice from the options above. Enter a choice 1 through {len(main_menu_items)} \n> ")
        self.execute_user_input(user_input, "main") #execute the user input
     
    def set_input_product_list(self, product_list, filename):
        self.input_product_list = product_list
        self.input_product_list_filename = filename

if __name__ == '__main__':
    input_file = "qvBox-warehouse-data-s23-v01.txt" #warehouse file
    try:
        myWarehouse = Warehouse(input_file) #instantiate the Warehouse object
    except:
        print(f"Warehouse data not found. File {input_file} was not found. Please put the file in the same directory as this program and try again.")
        sys.exit()
    myInterface = Interface(myWarehouse) #instantiate the Interface Object
    input_orders_list_filename = "qvBox-warehouse-orders-list-part01.txt"
    input_orders_list = [
                            [108335],
                            [108335, 391825, 340367, 286457, 661741],
                            [281610, 342706, 111873, 198029, 366109, 287261, 76283, 254489, 258540, 286457],
                            [427230, 372539, 396879, 391680, 208660, 105912, 332555, 227534, 68048, 188856, 736830, 736831, 479020, 103313, 1],
                            [633, 1321, 3401, 5329, 10438, 372539, 396879, 16880, 208660, 105912, 332555, 227534, 68048, 188856, 736830, 736831, 479020, 103313, 1, 20373],
                        ]
    try:
        with open(input_orders_list_filename, mode = "r") as input_orders_file: #open input_orders file
            input_orders_list = []
            orders = input_orders_file.readlines()
            for order in orders:
                input_orders_list.append([int(product.strip()) for product in order.split(",")])
    except: 
        input_orders_list_filename = "No input file was provided! Using default orders list."
    myInterface.set_input_product_list(input_orders_list, input_orders_list_filename)
    ascii_art = """
█   █ █▀▀ █   █▀▀ █▀▀█ █▀▄▀█ █▀▀ 　 ▀▀█▀▀ █▀▀█ 　 █▀▀█ █▀▀▀█ █▀▀█ █▀▀▀█ █▀▀█ █▀▀█ █▀▀█ ▀▀█▀▀ ▄ 
█ █ █ █▀▀ █   █   █  █ █ ▀ █ █▀▀ 　   █   █  █ 　 █▄▄▀ █   █ █▀▀▄ █   █ █    █▄▄█ █▄▄▀   █    
█▄▀▄█ ▀▀▀ ▀▀▀ ▀▀▀ ▀▀▀▀ ▀   ▀ ▀▀▀ 　   ▀   ▀▀▀▀ 　 █  █ █▄▄▄█ █▄▄█ █▄▄▄█ █▄▄█ █  █ █  █   █   ▀ 

█   █ █▀▀█ █▀▀█ █▀▀ █  █ █▀▀█ █  █ █▀▀ █▀▀ 　 █▄  █ █▀▀█ ▀█ █▀  ▀  █▀▀▀ █▀▀█ ▀▀█▀▀ █▀▀█ █▀▀█ 　 █▀▀█ █▀▀█ █▀▀█ 
█ █ █ █▄▄█ █▄▄▀ █▀▀ █▀▀█ █  █ █  █ ▀▀█ █▀▀ 　 █ █ █ █▄▄█  █▄█  ▀█▀ █ ▀█ █▄▄█   █   █  █ █▄▄▀ 　 █▄▄█ █  █ █  █ 
█▄▀▄█ ▀  ▀ ▀ ▀▀ ▀▀▀ ▀  ▀ ▀▀▀▀ ▀▀▀▀ ▀▀▀ ▀▀▀ 　 █  ▀█ ▀  ▀   ▀   ▀▀▀ ▀▀▀▀ ▀  ▀   ▀   ▀▀▀▀ ▀ ▀▀ 　 █  █ █▀▀▀ █▀▀▀
"""
    print(f"\n\n \033[32m{ascii_art}\033[0m")
    while(True):
        myInterface.display_main_menu()