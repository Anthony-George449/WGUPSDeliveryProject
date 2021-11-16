# Author: Anthony George
# Date: 10/8/2020
# Student ID: 000698822
#
# This program retrieves packages from packages.csv and distance between those packages from distance.csv and uses
# Dijkstra's shortest path in an algorithm to generate an mileage efficient route while following delivery instructions
# where necessary. (For more in-depth information regarding the algorithm, see line 590.)
#
# This program also includes a menu that allows the user to search for packages based on multiple parameters, allows the
# user to display a summary of all packages at any given time, adjust the business time, check how many miles have been
# elapsed with the current route, print all packages in order by id, and print all packages sorted by the route.
#
#
# The program also contains a handful of objects which are shared between multiple methods to make everything work.
# The way the program communicates and uses theses objects will be summarized below:
# p: Created using the HashMap class and importing data from packages.csv. This object contains all of the information
#   needed for the packages, the information being stored as a list inside a list of packages. This object is defined in
#   the main method and initialized by the method import_packages(). This object is able to be used throughout the
#   program without the need to pass it through parameters. It's only updated in the Main method, and it contains the
#   package information for the best route that was generated. This object is used in the menus to display selected
#   information about the packages to the user.
#
# p1: When initialized it copies all of the data from p. This object is able to be used throughout the program without
#   the need to pass it through parameters. It is used throughout the algorithm() to store each route that is generated.
#   When the route is generated a comparison is done between the route in p and the route in p1, and if p1 has the
#   better route, p1 is copied to p and p1 is overwritten with the next route to be used in the next comparison.
#
# hub_packages: A list initialized by appending each package from p to it. This object is able to be used throughout the
#   program without the need to pass it through parameters. It is used throughout the algorithm() as a list of packages
#   that remain in the hub. Everytime a package is routed, it is popped from hub_packages, so the program knows all the
#   packages have been routed when hub_packages is empty. hub_packages is reinitialized in Main before the algorithm()
#   is ran again for each loop.
#
# d: Created using the Graph class and importing data from distance.csv. This object contains all of the information
#   needed for the package distances. It contains a list with the names of all the vertexes (locations) and a list that
#   stores the weight (miles) between each vertex. This object is able to be used throughout the program without the
#   need to pass it through parameters. It is used in the algorithm to find the shortest path to the next package as
#   well as when the mileage and delivery times are updated.
#
# time: Initialized to 08:00:00 in the main menu. time is passed along through the program via method parameters and is
#   used in multiple ways. When passed to the algorithm() time is passed in twice and the algorithm() uses those times
#   plus recursion to update the times for each truck, keeping track of the en route and delivery times accurately.
#   When time is used in the algorithm() neither of the updated times are returned to the algorithm, so when the program
#   runs the main_menu() the time is still what is was initialized to.
#   When the time is used in the menus, the time is used as the current business time. This allows the user to update
#   time and use time in comparison to check statuses of packages.
#
# miles: Initialized to 0 in the main menu. miles is passed throughout the algorithm() via method parameters, and the
#   algorithm() returns miles after generating a route. miles is updated as the algorithm() recurses and holds the total
#   miles elapsed by a route. After being returned by the algorithm(), miles is used in a comparison with another object
#   miles_least, and is then set to 0 and sent through the algorithm() again until the loop it's in is done running.
#
# miles_least: Initialized to infinite in the main menu. miles_least contains the miles elapsed by the best route and is
#   passed throughout the menus using method parameters. After the algorithm() finishes running and returns miles,
#   miles_least is compared to miles, and if miles is less than miles_least, miles_least is updated to equal miles.
#   After the loop that calls the algorithm() is done running, miles_least contains the most efficient number of miles
#   (and p1 contains the route that miles_least refers to). miles_least is then passed throughout the menus so the user
#   can check how many miles have been elapsed by the current route.

# imports
import copy
import csv
import datetime
import math
from random import randrange


# The HashMap that all the packages are mapped to.
class HashMap:

    # Sets the size of the map (to 40 since there are 40 packages) and initializes it by mapping everything to None.
    def __init__(self):
        self.size = 40
        self.map = [None] * self.size

    # Since the first entry of self.map is at index 0 and the first package ID is 1 the key is adjusted here so the
    # package id can properly be used as the key.
    def get_hash(self, key):
        return key - 1

    # This adds a package to the hash map by first getting the package ID and using that as the key.
    # Once the key is set properly (using get_hash) the rest of the package information is mapped.
    def add(self, key, value):
        key_hash = self.get_hash(key)
        # Package information is added in the order: (Id, address, city, state, zip, weight, deadline,
        # delivery instructions, en route time (init to ''), delivery time (init to ''), and truck num (init to 0)).
        key_value = [key, value[1], value[2], value[3], value[4], value[6], value[5], '', '', '', 0]
        # Using the delivery note for each package the useful information is added to the proper spot (in the format of
        # a character identifying what the instruction asks for then the information needed to use the instruction).
        if 'Delayed on flight' in value[7]:
            key_value[7] = ('d: ' + value[7][51:])
        elif 'Wrong address' in value[7]:
            key_value[7] = 'a: 10:20 am'
        elif 'truck' in value[7]:
            key_value[7] = ('t: ' + value[7][21:])
        elif 'delivered with' in value[7]:
            key_value[7] = ('w: ' + value[7][23:])
        # If there is no delivery note for a package it is set to 'none'.
        else:
            key_value[7] = 'none'
        # The package is then added to the hash map.
        self.map[key_hash] = key_value

    # Returns the package as a proper vertex so the edge weights can be retrieved without error.
    def get_vertex(self, key):
        key_hash = self.get_hash(key)
        return ' '+self.map[key_hash][1]+' ('+self.map[key_hash][4]+')'

    # This removes a package from the hash map by getting the proper key with get_hash, then checking that a package
    # is mapped to the location and setting it to None if it is.
    #
    # Unused in the program currently, but useful to have in case it's ever needed.
    def delete(self, key):
        key_hash = self.get_hash(key)
        if self.map[key_hash] is not None:
            self.map[key_hash] = None

    # Allows the program to update the truck number for a package.
    def truck_num(self, key, truck_num):
        key_hash = self.get_hash(key)
        self.map[key_hash][10] = truck_num

    # Allows the program to add a delivery time to a package.
    def delivery_time(self, key, time):
        key_hash = self.get_hash(key)
        self.map[key_hash][9] = ('Delivered: '+time)

    # Allows the program to add a delivery time to a package.
    def enroute_time(self, key, time):
        key_hash = self.get_hash(key)
        self.map[key_hash][8] = ('En Route: ' + time)

    # Allows the program to add linked packages going a second way. For example, if package 14 has to be delivered with
    # package 15 and 19 then this method will update packages 15 and 19 so they must be delivered with package 14,
    # since the delivery instructions only go one way on their own.
    #
    # This may not work with other data sets since this relies on the packages being updated not having delivery
    # instructions beforehand. Which means the packages can't be delayed, have a wrong address, or be designated to a
    # specific truck. In order to change this I would just have to make packages be able to have multiple delivery
    # instructions, but that is out of the scope for this project.
    def add_linked_package(self, key):
        key_hash = self.get_hash(key)
        # First, the packages that need to be linked are saved to a list from the delivery instructions.
        linked_packages = self.map[key_hash][7][3:].split(", ")
        # Then that list is looped through.
        for package in linked_packages:
            # The index for the package to be linked is saved.
            p = int(package) - 1
            # If the package to be linked doesn't have delivery instructions then instructions to be linked with the
            # current package are added.
            if self.map[p][7] == 'none':
                self.map[p][7] = 'w: ' + str(key)
            # If the package already has instructions linking it to other packages, those packages are saved to a list.
            elif self.map[p][7][0] == 'w':
                linked_packages_2 = self.map[p][7][3:].split(", ")
                # Then the program checks if the current package is already in the list, adding it to the delivery
                # instructions if it is not.
                if str(key) not in linked_packages_2:
                    self.map[p][7] += ', ' + str(key)

    # Allows the program to update an address for a package.
    def update_address(self, key, address, city, state, zip):
        key_hash = self.get_hash(key)
        self.map[key_hash][1] = address
        self.map[key_hash][2] = city
        self.map[key_hash][3] = state
        self.map[key_hash][4] = zip

    # Allows the program to search through the list of packages. The value allows the user to specify what they're
    # searching for (Id, address, etc.) and the search is the search term.
    def search(self, value, search, time):
        print('\n----Results----')
        # checks every item in the hash map
        for item in self.map:

            # If the user is searching for ID or weight, the program should only return exact matches (Package with ID
            # 10 shouldn't be returned when searching for ID = 1)
            if value == 1 or value == 6:
                if search == str(item[value - 1]):
                    self.print_from_time(time, item)

            # If the user searches for the delivery status then first the search term is checked, and then the package
            # and status information is printed if using the saved delivery and en route times.
            elif value == 8:
                # Retrieves the delivery time from the package information.
                t = datetime.datetime.strptime(item[9][11:], "%H:%M:%S")
                delivery_time = datetime.timedelta(hours=t.hour, minutes=t.minute, seconds=t.second)
                # Retrieves the en route time from the package information.
                t = datetime.datetime.strptime(item[8][10:], "%H:%M:%S")
                enroute_time = datetime.timedelta(hours=t.hour, minutes=t.minute, seconds=t.second)
                # If the user wants to see all packages at the hub, the program prints the package's info when the
                # en route time is greater than the current time, meaning that package is still at the hub.
                if 'Hub' == search or 'hub' == search:
                    if enroute_time > time:
                        print('Package: ' + str(item[0]) + ' | Address: ' + str(item[1]) + ', ' + str(
                            item[2]) + ', ' + str(item[3]) + ', ' + str(item[4]) + ' | Weight: ' + str(item[5])
                            + ' | Status: Hub' + ' | Deadline: ' + str(item[6]))
                # If the user wants to see delivered packages, the program prints the package's info when the delivery
                # time is less than or equal to the current time, meaning the package has been delivered.
                elif 'Delivered' == search or 'delivered' == search:
                    if delivery_time <= time:
                        print('Package: ' + str(item[0]) + ' | Address: ' + str(item[1]) + ', ' + str(
                            item[2]) + ', ' + str(item[3]) + ', ' + str(item[4]) + ' | Weight: ' + str(item[5])
                              + ' | Status: ' + str(item[9]) + ' | Deadline: ' + str(item[6]))
                # If the user wants to see packages that are en route, the program prints the package's info when the
                # en route time is less than or equal to the current time and the delivery time is greater than the
                # current time, meaning the package is en route.
                elif 'En Route' == search or 'En route' == search or 'en route' == search:
                    if enroute_time <= time < delivery_time:
                        print('Package: ' + str(item[0]) + ' | Address: ' + str(item[1]) + ', ' + str(
                            item[2]) + ', ' + str(item[3]) + ', ' + str(item[4]) + ' | Weight: ' + str(item[5])
                              + ' | Status: ' + str(item[8]) + ' | Deadline: ' + str(item[6]))

            # If the user searches for anything else then it's search using 'in', so if they search for something like
            # 'Main' for the address, '123 Main St.' and '485 Main St.' will both be returned.
            elif search in str(item[value - 1]):
                self.print_from_time(time, item)

    # This method is used alongside search() to properly obtain the package status for printing
    def print_from_time(self, time, item):
        # Retrieves the delivery time from the package information.
        t = datetime.datetime.strptime(item[9][11:], "%H:%M:%S")
        delivery_time = datetime.timedelta(hours=t.hour, minutes=t.minute, seconds=t.second)
        # Retrieves the en route time from the package information.
        t = datetime.datetime.strptime(item[8][10:], "%H:%M:%S")
        enroute_time = datetime.timedelta(hours=t.hour, minutes=t.minute, seconds=t.second)
        # If the en route time is greater than the current time, then the package is still at the hub, so the package
        # information is printed with that as the status.
        if enroute_time > time:
            print('Package: ' + str(item[0]) + ' | Address: ' + str(item[1]) + ', ' + str(
                item[2]) + ', ' + str(item[3]) + ', ' + str(item[4]) + ' | Weight: ' + str(item[5])
              + ' | Status: Hub' + ' | Deadline: ' + str(item[6]))
        # If the delivery time is less than or equal than the current time, then the package is still at the hub, so
        # the package information is printed with that as the status.
        elif delivery_time <= time:
            print('Package: ' + str(item[0]) + ' | Address: ' + str(item[1]) + ', ' + str(
                item[2]) + ', ' + str(item[3]) + ', ' + str(item[4]) + ' | Weight: ' + str(item[5])
                  + ' | Status: ' + str(item[9]) + ' | Deadline: ' + str(item[6]))
        # If the en route time is less than or equal to the current time and the delivery time is greater than the
        # current time, then the package is still at the hub, so the package information is printed with that as the
        # status.
        elif enroute_time <= time < delivery_time:
            print('Package: ' + str(item[0]) + ' | Address: ' + str(item[1]) + ', ' + str(
                item[2]) + ', ' + str(item[3]) + ', ' + str(item[4]) + ' | Weight: ' + str(item[5])
                  + ' | Status: ' + str(item[8]) + ' | Deadline: ' + str(item[6]))

    # This method prints out -----Packages----- and then all of the mapped packages below, skipping the entries that are
    # None. Nothing in the hash map will be None in this case, but it's useful to have in case any updates change that.
    def print(self):
        print('-----Packages-----')
        for item in self.map:
            if item is not None:
                print(str(item))

    # This method records the list of packages in delivery order so the program can print all the packages in a way
    # where the user can easily see the route.
    def print_route(self):
        # First, all the packages are copied to a list so pop() can be used on the list to empty it.
        packages = []
        for item in self.map:
            packages.append(item)
        # A second, empty list is also created.
        list = []

        # This loops until the copied list is empty.
        while len(packages) != 0:
            # First the first package index is selected.
            index = 0
            # Then all packages remaining in the copied list are looped through.
            for i in range(0, len(packages)):
                # The indexed package's en route time is saved.
                t = datetime.datetime.strptime(packages[index][8][10:], "%H:%M:%S")
                enroute_time = datetime.timedelta(hours=t.hour, minutes=t.minute, seconds=t.second)
                # Package i's en route time is also saved.
                t = datetime.datetime.strptime(packages[i][8][10:], "%H:%M:%S")
                i_enroute_time = datetime.timedelta(hours=t.hour, minutes=t.minute, seconds=t.second)

                # The first comparison is if package i is en route before the indexed package. If so, then i becomes
                # the new indexed package, since it would be delivered first.
                if enroute_time > i_enroute_time:
                    index = i
                # If the packages are en route at the same time...
                elif enroute_time == i_enroute_time:
                    # Then the truck numbers are compared, and packages on truck 1 are saved with priority over truck 2
                    # so truck 1's route will be listed before truck 2 if both are en route at the same time.
                    if packages[index][10] > packages[i][10]:
                        index = i
                    # If the truck numbers are the same, then the delivery time needs to be compared.
                    elif packages[index][10] == packages[i][10]:
                        # The indexed package's delivery time is saved.
                        t = datetime.datetime.strptime(packages[index][9][11:], "%H:%M:%S")
                        delivery_time = datetime.timedelta(hours=t.hour, minutes=t.minute, seconds=t.second)
                        # Package i's delivery time is also saved.
                        t = datetime.datetime.strptime(packages[i][9][11:], "%H:%M:%S")
                        i_delivery_time = datetime.timedelta(hours=t.hour, minutes=t.minute, seconds=t.second)

                        # If package i is delivered before the indexed package, then package i is saved as the indexed
                        # package.
                        if delivery_time > i_delivery_time:
                            index = i

            # The package that is delivered first on the lowest number truck is now saved to index, so that package
            # is popped from the packages list onto the list to be printed.
            list.append(packages.pop(index))

        # Once the packages list is empty, it means all the packages are sorted by delivery time/truck number so they
        # can be printed in proper order.
        print('-----Packages-----')
        # First, the en route time and the truck number for the first package are saved.
        t = datetime.datetime.strptime(list[0][8][10:], "%H:%M:%S")
        enroute_time = datetime.timedelta(hours=t.hour, minutes=t.minute, seconds=t.second)
        truck_num = list[0][10]
        # Then the truck number is printed, to let the user know which truck is being displayed.
        print('Truck ' + str(truck_num) + ':')

        # Then every item in the list is looped through.
        for item in list:
            # The item's en route time is saved.
            t = datetime.datetime.strptime(item[8][10:], "%H:%M:%S")
            item_enroute_time = datetime.timedelta(hours=t.hour, minutes=t.minute, seconds=t.second)
            # The current item's en route time is compared to the saved en route time as well as the current item's
            # truck number and the saved truck number. If either of these aren't equal then the items being compared are
            # part of different shipments, so a new line and then text identifying the truck are printed, to break up
            # the shipments.
            if enroute_time != item_enroute_time or truck_num != item[10]:
                print('\nTruck ' + str(item[10]) + ':')
            # After that, the item is printed and then that item's en route time is saved to enroute_time and it's truck
            # number is saved to truck_num so it can be used in the next comparison.
            print(str(item))
            enroute_time = item_enroute_time
            truck_num = item[10]
        # At the end of the loop every package has been printed.

    # Prints the Package #, Delivery status and then all package information, as well as a summary of how many packages
    # are at the hub, en route, and being delivered.
    def print_status(self, time):
        # Counts for the statuses of the packages are set to 0.
        hub = 0
        enroute = 0
        delivered = 0
        # This loop saves the delivery and en route times for each package and compares them to the current time,
        # adding 1 to the proper count depending on the status of the package.
        #
        # Also prints out the current package's number and status before printing all information for the package.
        for item in self.map:
            # Retrieves the delivery time from the package information.
            t = datetime.datetime.strptime(item[9][11:],"%H:%M:%S")
            delivery_time = datetime.timedelta(hours=t.hour, minutes=t.minute, seconds=t.second)
            # Retrieves the en route time from the package information.
            t = datetime.datetime.strptime(item[8][10:],"%H:%M:%S")
            enroute_time = datetime.timedelta(hours=t.hour, minutes=t.minute, seconds=t.second)
            # Compares the delivery time and en route time to the current time, printing the package info and updating
            # the count where needed.
            if delivery_time <= time:
                print('Package #' + str(item[0]) + ', Status: Delivered')
                print(str(item))
                delivered += 1
            elif enroute_time <= time:
                print('Package #' + str(item[0]) + ', Status: En Route')
                print(str(item))
                enroute += 1
            else:
                print('Package #' + str(item[0]) + ', Status: At the Hub')
                print(str(item))
                hub += 1

        # All the counts contain the proper number of packages with each status, so that information is also printed.
        print('\nStatus Summary:')
        print(str(hub) + ' Package(s) at the Hub\n' +
              str(enroute) + ' Package(s) En Route\n' +
              str(delivered) + ' Package(s) Delivered')


# The graph for adding the distance table into the program.
class Graph:

    # Initializes the list of vertices and the list of edges between them.
    def __init__(self):
        self.vertex_list = {}
        self.edge_weights = {}

    # Adds a vertex to the list of vertices.
    def add_vertex(self, vertex):
        self.vertex_list[vertex] = []

    # Adds an edge between 2 vertexes. Uses the vertex indices to identify the proper vertices
    # and adds them to the list of edges with the proper edge weight.
    def add_edge(self, vertex_index_a, vertex_index_b, weight=1.0):
        # First loop to get the first vertex.
        count = 0
        for item in self.vertex_list:
            if count == vertex_index_a:
                vertex_a = item
                break
            count += 1

        count = 0
        # Second loop to get the second vertex.
        for item in self.vertex_list:
            if count == vertex_index_b:
                vertex_b = item
                break
            count += 1

        # Adds the two vertexes to the edge_weights list, with the weight as their value.
        self.edge_weights[(vertex_a, vertex_b)] = weight
        # Also adds vertex_b as a value of vertex_a in the vertex_list.
        self.vertex_list[vertex_a].append(vertex_b)
        # Since the edges are all undirected, vertex_a and vertex_b are added to the edge_weights  and vertex_list
        # again, but in reverse order. The if statement prevents adding duplicates (ex. Hub -> Hub and Hub <- Hub).
        if weight != 0.0:
            self.edge_weights[(vertex_b, vertex_a)] = weight
            self.vertex_list[vertex_b].append(vertex_a)

    # Returns a specific pair of vertices edge weight.
    def get_weight(self, vertex_address_a, vertex_address_b):
        return self.edge_weights[(vertex_address_a, vertex_address_b)]

    # Returns a specific vertex identified by an index.
    def get_vertex(self, vertex_index):
        count = 0
        for item in self.vertex_list:
            if count == vertex_index:
                break
            count += 1
        return (item)

    # Prints all the vertices from the vertex_list. Unused currently, but useful to have when updating the program.
    def print_list(self):
        for item in self.vertex_list:
            print(item)


# Importing the packages from the packages.csv file
def import_packages():
    # Initializes a HashMap to save the packages to
    h = HashMap()

    # Adds every row in the file to the HashMap as a package
    with open('packages.csv') as csvfile:
        readCSV = csv.reader(csvfile, delimiter=',')

        for row in readCSV:
            h.add(int(row[0]), row)
    csvfile.close()

    # Once all the packages are added, any with instructions linking to other packages are ran through a method to make
    # the instructions two way. (Package 14 links to 15 and 19, but neither 15 or 19 link to 14 so that needs to be
    # updated.)
    for item in h.map:
        if item[7][0] == 'w':
            h.add_linked_package(item[0])

    # A notification stating that the packages have been imported is printed, and the hash map is returned.
    print('Packages imported')
    return h


# Importing the distances from the distances.csv file.
def import_distances():
    # Initializes a graph to map the vertices and edge weights to.
    g = Graph()

    # Adds all the data from distance.csv to the graph.
    with open('distance.csv') as csvfile:
        readCSV = csv.reader(csvfile, delimiter=',')

        # count1 refers to the first vertex being used in add_edge().
        count1 = 0
        for row in readCSV:
            # First, the vertex is saved to the vertex list.
            g.add_vertex(row[1])
            # count2 refers to the second vertex being used in add_edge().
            count2 = 2
            # Then each weight is added to the edge weight list
            while count2 < len(row):
                if row[count2] != '':
                    g.add_edge(count1, count2 - 2, float(row[count2]))
                # Incrementing count1 and count2 makes sure every vertex is added to the edge weight list.
                count2 += 1
            count1 += 1
    csvfile.close()

    # A notification stating that the distances have been imported is printed, and the graph is returned.
    print('Distance table imported')
    return g


# The main menu interface. The objects time is kept track of so the user can adjust the time as desired to see the
# status of packages at different times. Miles is also kept track of so the user can view the miles elapsed by the route
# generated by the algorithm.
#
# The main menu allows the user to choose between 7 options.
# 1 sends them to the Search Packages menu.
# 2 prints out the current program time, each package number and status, as well as each package's information, and
#   how many packages are at the hub, en route, or delivered.
# 3 allows the user to adjust the program time so they can view how package statuses at different times.
# 4 displays the total miles traveled by the generated route.
# 5 prints all of the packages in order by package ID.
# 6 prints all packages sorted by shipment, allowing the user to see the route easier.
# 7 does nothing, therefore letting the program finish execution.
def main_menu(time, miles):
    print('\n\n\n\n\n------------Main Menu------------')
    print('Current Time: ' + str(time))
    print('\nWelcome to WGUPS, what would you like to do?')
    print('1. Search Packages')
    print('2. Get Status Summary')
    print('3. Adjust Time')
    print('4. Check Miles')
    print('5. Print Packages by Package ID')
    print('6. Print Packages in delivery order')
    print('7. Exit')
    value = input('\nEnter a corresponding number: ')

    # This while loop ensures the user enters a proper menu selection.
    while value not in {'1', '2', '3', '4', '5', '6', '7'}:
        value = input('Invalid selection. Please enter a valid number: ')

    # If the user enters 1, goes to the search menu.
    if value == '1':
        search_menu(time, miles)

    # If the user enters 2, prints the status of all packages as well the current program time before returning to the
    # main menu.
    elif value == '2':
        print('Current time: ' + str(time))
        p.print_status(time)
        input('\nPress enter to continue...')
        main_menu(time, miles)

    # If the user enters 3, allows them to enter a new time before returning to the main menu.
    elif value == '3':
        new_time = input('Enter the new time (in the format of 20:00:00): ')
        t = datetime.datetime.strptime(new_time, "%H:%M:%S")
        time = datetime.timedelta(hours=t.hour, minutes=t.minute, seconds=t.second)
        main_menu(time, miles)

    # If the user enters 4, the total miles elapsed will be displayed, which can be used to see how efficient of a route
    # the algorithm generates. After displaying this the user will return to the main menu.
    elif value == '4':
        print('A total of ' + str(miles) + ' miles will be traveled with the current route')
        input('\nPress enter to continue...')
        main_menu(time, miles)

    # If the user enters 5, all packages are printed in Package ID order.
    elif value == '5':
        p.print()
        input('\nPress enter to continue...')
        main_menu(time, miles)

    # If the user enters 6, all packages are printed, sorted by shipment.
    elif value == '6':
        p.print_route()
        input('\nPress enter to continue...')
        main_menu(time, miles)


# The search packages interface. Allows the user to specify what they'd like to search for and then enter a search term.
# The program will then print out the corresponding packages and return to the main menu.
def search_menu(time, miles):
    print('\n\n\n\n\n------------Search Packages------------')
    print('Current Time: ' + str(time))
    print('1. ID')
    print('2. Address')
    print('3. City')
    print('4. State')
    print('5. Zip')
    print('6. Weight')
    print('7. Deadline')
    print('8. Status')
    print('9. Return to Main Menu')
    value = input('\nEnter a corresponding number to search by: ')

    # This while loop ensures the user enters a proper menu selection.
    while value not in {'1', '2', '3', '4', '5', '6', '7', '8', '9'}:
        value = input('Invalid selection. Please enter a valid number: ')

    # If the user enters 9, the program just returns to the main menu.
    if value == '9':
        main_menu(time, miles)

    # Otherwise, the program prompts the user for a search term and runs p.search() before returning to the main menu.
    else:
        search = input('Please enter a search term: ')
        p.search(int(value), search, time)
        input('\nPress enter to continue...')
        main_menu(time, miles)


# The algorithm used to determine a route for delivering the packages.
# Dijkstra's shortest path is used to obtain the shortest path between the current location and the next package,
# which aims to give a route using a low number of miles.


# Space-Time Complexity:
# This algorithm will run in O(N^2) time.
# The code for this algorithm ends up boiling down to something like:
#
# algorithm():
#   while(len(hub_packages) > 0 and len(truck) < truck_len):
#       for i in range(0, len(hub_packages):
#           smallest_index = i
#       hub_packages.pop(smallest_index)
#   if (len(hub_packages) != 0):
#       algorithm()
#
# The N in this case is the len(hub_packages). Though not in one go, the while loop ends up running N times, a few times
# each time algorithm() recurses, until len(hub_packages) == 0. The for loop also runs N times every time it's called,
# and it's called every time the while loop loops. This means that overall, everything runs N * N times which is N^2.
# Meaning the space-time complexity is O(N^2).


# Logic used for the algorithm:
# First, a random number between 6 (arbitrary minimum I chose) and 16 is chosen as the size of the truck. A truck can
# hold up to 16 packages, but 16 might not be the most optimal number of packages to load every time, so the randomness
# will give different, potentially better results every time the algorithm() is ran.
#
#
# After generating the truck size, Dijkstra's shortest path is implemented to fill up the truck.
# Now, a package must be chosen as the first delivery point. This first point must have it's own block of code because
# instead of comparing the distance between 2 packages, the program is checking the distance from the hub. So a section
# of code that compares the distance from the hub to that package is used, and after comparing all packages, the closest
# one is saved. The en route time for the package is also updated.
#
# In order to avoid choosing an invalid package, the starting index (the package used in the first comparison) can't be
# set until a valid package is found. So, the index to be saved is initialized to an unreal index (-1) and is updated
# when the first valid package is found. Since the section that will need to compare packages will confirm that the
# package being checked against the starting index is valid, that section can be used to update the starting index when
# it finds the first valid package. After that, it can continue on, comparing each package to the starting index, saving
# the closest package to the starting index and looping until all packages have been checked.
#
# If the starting index was updated, then the closest, valid package has been found, so that package can be loaded onto
# the truck. Otherwise, the time needs to be adjusted, since the only constraint invalidating packages is time, so the
# program will skip loading the truck and adjust the time.
#
# If the package that was loaded was a package that's linked to other packages, then the linked packages are also loaded
# onto the truck.
#
#
# Now that the first package has been loaded, the rest of the comparisons will be between packages, so only one section
# of code is needed to finish loading the truck. This section will run similarly to the previous one, with the need to
# find a valid starting index being the same. The distance from the previous package to the next will be compared, and
# the closest one will be saved.
#
# This section does have to have a copy made and modified slightly to prioritize packages with deadlines (urgent
# packages). Instead of just loading the rest of the packages, a number of urgent packages should be to the truck to
# decrease the chances of missing any deadlines. So, some urgent packages will be loaded first (using another random
# number since there's no way to know what the best number is) and the rest of the truck will be loaded with the
# remaining packages.
#
#
# Once the truck has hit it's capacity (the randomly generated length) or all packages have been delivered, the program
# can continue. First, the program will have to check that the starting index was updated, because if it wasn't then
# the remaining packages are being constrained by time. So, some time has to be added to allow those packages to be
# delivered. The program will also verify that the truck is valid (ensure it didn't surpass the maximum size of 16)
# before continuing. Once everything is validated, the program needs to now record the time each package will be
# delivered at and record the total miles. So, a method that goes through all the packages in the truck is ran and it
# calculates the time and miles elapsed using the mph and edge weights. Since this is where the time is updated, this is
# where the program checks for any late packages, throwing out the route if one is found.
#
#
# After the en route and delivery times have been added for all the packages, or the time has been adjusted, the
# algorithm will recurse and repeat until all of the packages have been delivered


# Hindsight and what I would like to change in the future:
#
# In hindsight, I could have added the hub as a dummy package to the start of the truck and use one section of code to
# load all of the packages instead of one for the first and another for the rest. That would require reworking a good
# portion of the code, and would mostly just make the code more tidy, not adding much, if any, optimization.
#
# Another thing I realized towards the end of developing this code was a large amount of optimization I missed that
# would require reworking a lot of code to implement. As of now, the program adds urgent packages and linked packages
# side by side, without putting any packages in between. As an example, packages 14, 15, 16, and 20 are all linked and
# generally get delivered in that order. Packages 15 and 16 have the same address and another package, 34, shares that
# address with them. However, the way I implemented the linked (and urgent) packages, package 34 will never be delivered
# alongside 15 and 16 even though it can and should be. In order to make this work I would have to make the program
# check if any packages can be inserted in between already routed packages instead of just at the end.
#
# Another similar thing I realized towards the end of development was that same addressed packages aren't always
# delivered together due to the truck size. One example I've seen is package 2 being added as the last package in truck
# 1 and package 33 being added as the first package in truck 2 even though packages 2 and 33 share the same address and
# have no constraints. In order to fix this I could add delivery instructions to link those packages, but if these
# packages already have delivery instructions there could be conflicts. Another method I could use to fix this is just
# adding any packages with the same address to the end of the truck (if 2 is the last package in truck 1 just add 33 to
# truck 1 as well). Since the truck_len is random there's a good chance that adding an extra 1 or 2 packages wouldn't
# cause it to go over the maximum size (16) and I could add a check for that to prevent that or just throw out the route
# if it surpasses the maximum size. In the future I would like to try to implement one or both of these solutions and
# see the results.
#
# One other thing I noticed was that since I only compare the next package to be added to the previous one the last
# package might not be the best fit always. The truck has to return to the hub after delivering all the packages, so it
# could be better to check the distance from the previous package to the current package to the hub instead of just from
# the previous package to the current package for the final package. This might optimize a bit of mileage and would be
# implemented similarly to putting packages in between linked and urgent packages.
def algorithm(time1, time2, miles, truck_num):
    # First, an empty list used as the truck is initialized.
    truck = []
    # The truck number is also set, this assignment sets the truck number to 1 or 2, switching every recursion.
    truck_num = (truck_num % 2) + 1
    # A random number between 6 (arbitrary minimum I chose) and 16 is generated as the number of packages to be loaded
    # on the truck.
    truck_len = randrange(6, 16)
    # Since truck 1 and 2 can deliver at the same time, 2 different times are stored and used based on which truck
    # is currently being routed.
    if truck_num == 1:
        time = time1
    elif truck_num ==2:
        time = time2

    # First, the package that is closest to the hub, and is able to be delivered is obtained.
    #
    # smallest_index is initialized to -1. If a valid package is found, it will be updated later on.
    smallest_index = -1
    # All packages are looped through to find the closest one to the hub.
    for i in range(0, len(hub_packages)):
        # This section stores the time a delayed/incorrect package can be delivered after.
        if hub_packages[i][7][0] == 'd' or hub_packages[i][7][0] == 'a':
            t = datetime.datetime.strptime(hub_packages[i][7][3:-3], "%H:%M")
            delay_time = datetime.timedelta(hours=t.hour, minutes=t.minute)
        # If the package isn't delayed, then delay_time is set to time so the package can be validated.
        else:
            delay_time = time

        # This section checks if any packages with the wrong address can be corrected, and corrects them if they can be.
        if hub_packages[i][7][0] == 'a' and delay_time <= time:
            # Since there's only one package that has a wrong address I just manually corrected the address.
            # In order to make this applicable to other data sets I would add something like:
            # value = input('Package #'+str(i+1)+' contained an incorrect address. WGUPS has received the correct
            # address, please enter the correct address now: ')
            # in order to have the user enter the updated information, but updating it manually works for this case.
            p1.update_address(hub_packages[i][0], '410 S State St', 'Salt Lake City', 'UT', '84111')

        # If the package needs to be delivered on a specific truck then that truck number is saved.
        # If there's no truck number specified, then the truck number is set to the current truck so the program will
        # recognize that the package can be loaded onto the current truck.
        if hub_packages[i][7][0] == 't':
            truck_num_p = int(hub_packages[i][7][3:])
        else:
            truck_num_p = truck_num

        # This if statement checks to see if the package can be delivered, and if it can be delivered on the current
        # truck.
        if delay_time <= time and truck_num_p == truck_num:
            # If smallest_index is -1, then a valid starting point hasn't been found yet. i is a valid starting point,
            # so smallest_index is set to i.
            if smallest_index == -1:
                smallest_index = i
            # This part compares two packages distances from the hub. Whichever one is closest has it's index saved and
            # after all packages have been compared we have the index for the package to be added to the truck.
            else:
                if d.get_weight(' HUB', p1.get_vertex(hub_packages[i][0])) < \
                        d.get_weight(' HUB', p1.get_vertex(hub_packages[smallest_index][0])):
                    smallest_index = i

    # If smallest_index is still -1, then there was no valid starting point, meaning the time needs to be adjusted, so
    # this section, which adds the package smallest_index refers to, must be skipped.
    if smallest_index != -1:
        # After all packages have been compared the closest one is popped from the hub_packages list and saved.
        current_vertex = hub_packages.pop(smallest_index)
        # Then, the properly named vertex (for comparing weights between locations) is saved.
        curr_v_vertex = p1.get_vertex(current_vertex[0])
        # The closest package is added to the truck.
        truck.append(current_vertex)
        # The time that the package will leave the hub is updated.
        p1.enroute_time(current_vertex[0], str(time))

        # This checks if the current vertex has to be delivered with other packages, and if it does, it runs a
        # method to add the linked packages.
        if current_vertex[7][0] == 'w':
            # The method to add the linked packages is called.
            truck = linked_list(time, truck, current_vertex, curr_v_vertex)
            # Saves the last package added to the truck as the current vertex so the program can continue as normal.
            current_vertex = truck[len(truck) - 1]
            # Then, the properly named vertex (for comparing weights between locations) is saved.
            curr_v_vertex = p1.get_vertex(current_vertex[0])

    # After obtaining a starting package, some urgent packages are added to the truck (the number is decided with a
    # random range spanning from 2 (arbitrary minimum) to the length of the truck). The added packages are added by
    # ensuring they are valid, have a deadline, and are the closest to the current package.
    #
    # If smallest_index equals -1, then the program was unable to find a valid starting point, so this whole section
    # must be skipped.
    if smallest_index != -1:
        # A random number between 2 (arbitrary minimum number I chose) and the random truck length is selected
        # as the number of packages with deadlines that will be loaded.
        # I did this because there's no way to know what combination of urgent and non-urgent packages will give the
        # most efficient route.
        random = randrange(2, truck_len)
        # This will loop until either the hub_packages list is empty or the packages loaded equals the random number of
        # urgent packages to be loaded.
        while len(hub_packages) > 0 and len(truck) < random:
            # smallest_index is set to -1. If a valid package is found, it will be updated later on.
            smallest_index = -1
            for i in range(0, len(hub_packages)):
                # This section stores the time a delayed/incorrect package can be delivered after.
                if hub_packages[i][7][0] == 'd' or hub_packages[i][7][0] == 'a':
                    t = datetime.datetime.strptime(hub_packages[i][7][3:-3], "%H:%M")
                    delay_time = datetime.timedelta(hours=t.hour, minutes=t.minute)
                # If the package isn't delayed, then delay_time is set to time so the package can be validated.
                else:
                    delay_time = time

                # If the package needs to be delivered on a specific truck then that truck number is saved.
                # If there's no truck number specified, then the truck number is set to the current truck so the program
                # will recognize that the package can be loaded onto the current truck.
                if hub_packages[i][7][0] == 't':
                    truck_num_p = int(hub_packages[i][7][3:])
                else:
                    truck_num_p = truck_num

                # This if statement checks to see if the package can be delivered, has a deadline, and if it can be
                # delivered on the current truck.
                if delay_time <= time and hub_packages[i][6] != 'EOD' and truck_num_p == truck_num:
                    # If smallest_index is -1, then a valid starting point hasn't been found yet. i is a valid starting
                    # point, so smallest_index is set to i.
                    if smallest_index == -1:
                        smallest_index = i
                    # This part compares two packages distances from the hub. Whichever one is closest has it's
                    # index saved and after all packages have been compared we have the index for the package to be
                    # added to the truck.
                    else:
                        if d.get_weight(curr_v_vertex, p1.get_vertex(hub_packages[i][0])) < \
                                d.get_weight(curr_v_vertex, p1.get_vertex(hub_packages[smallest_index][0])):
                            smallest_index = i

            # If smallest_index is still -1, then there was no valid starting point, meaning the time needs to be
            # adjusted, so this section, which adds the package smallest_index refers to, must be skipped.
            if smallest_index != -1:
                # After all packages have been compared the closest one is popped from the hub_packages list and saved.
                current_vertex = hub_packages.pop(smallest_index)
                # Then, the properly named vertex (for comparing weights between locations) is saved.
                curr_v_vertex = p1.get_vertex(current_vertex[0])
                # The closest package is added to the truck.
                truck.append(current_vertex)
                # The time that the package will leave the hub is updated.
                p1.enroute_time(current_vertex[0], str(time))

                # This checks if the current vertex has to be delivered with other packages, and if it does, it runs a
                # method to add the linked packages.
                if current_vertex[7][0] == 'w':
                    # The method to add the linked packages is called.
                    truck = linked_list(time, truck, current_vertex, curr_v_vertex)
                    # Saves the last package added to the truck as the current vertex so the program can continue as
                    # normal.
                    current_vertex = truck[len(truck) - 1]
                    # Then, the properly named vertex (for comparing weights between locations) is saved.
                    curr_v_vertex = p1.get_vertex(current_vertex[0])
            # If there's no valid starting point, then the program needs to break out of the while loop, otherwise it
            # will get stuck in an infinite loop.
            else:
                break

        # Once all the urgent packages have been added, or if there are none to be added, the rest of the packages are
        # added, ensuring they are valid and closest to the current package.
        #
        # This will loop until either the hub_packages list is empty or the packages loaded equals the random number of
        # urgent packages to be loaded.
        while len(hub_packages) > 0 and len(truck) < truck_len:
            # smallest_index is set to -1. If a valid package is found, it will be updated later on.
            smallest_index = -1
            for i in range(0, len(hub_packages)):
                # This section stores the time a delayed/incorrect package can be delivered after.
                if hub_packages[i][7][0] == 'd' or hub_packages[i][7][0] == 'a':
                    t = datetime.datetime.strptime(hub_packages[i][7][3:-3], "%H:%M")
                    delay_time = datetime.timedelta(hours=t.hour, minutes=t.minute)
                # If the package isn't delayed, then delay_time is set to time so the package can be validated.
                else:
                    delay_time = time

                # If the package needs to be delivered on a specific truck then that truck number is saved.
                # If there's no truck number specified, then the truck number is set to the current truck so the program
                # will recognize that the package can be loaded onto the current truck.
                if hub_packages[i][7][0] == 't':
                    truck_num_p = int(hub_packages[i][7][3:])
                else:
                    truck_num_p = truck_num

                # This if statement checks to see if the package can be delivered, and if it can be delivered on the
                # current truck.
                if delay_time <= time and truck_num_p == truck_num:
                    # If smallest_index is -1, then a valid starting point hasn't been found yet. i is a valid starting
                    # point, so smallest_index is set to i.
                    if smallest_index == -1:
                        smallest_index = i
                    # This part compares two packages distances from the hub. Whichever one is closest has it's index
                    # saved and after all packages have been compared we have the index for the package to be added to
                    # the truck.
                    else:
                        if d.get_weight(curr_v_vertex, p1.get_vertex(hub_packages[i][0])) < \
                                d.get_weight(curr_v_vertex, p1.get_vertex(hub_packages[smallest_index][0])):
                            smallest_index = i

            # If smallest_index is still -1, then there was no valid starting point, meaning the time needs to be
            # adjusted, so this section, which adds the package smallest_index refers to, must be skipped.
            if smallest_index != -1:
                # After all packages have been compared the closest one is popped from the hub_packages list and saved.
                current_vertex = hub_packages.pop(smallest_index)
                # Then, the properly named vertex (for comparing weights between locations) is saved.
                curr_v_vertex = p1.get_vertex(current_vertex[0])
                # The closest package is added to the truck.
                truck.append(current_vertex)
                # The time that the package will leave the hub is updated.
                p1.enroute_time(current_vertex[0], str(time))

                # This checks if the current vertex has to be delivered with other packages, and if it does, it runs a
                # method to add the linked packages.
                if current_vertex[7][0] == 'w':
                    # The method to add the linked packages is called.
                    truck = linked_list(time, truck, current_vertex, curr_v_vertex)
                    # Saves the last package added to the truck as the current vertex so the program can continue as
                    # normal.
                    current_vertex = truck[len(truck) - 1]
                    # Then, the properly named vertex (for comparing weights between locations) is saved.
                    curr_v_vertex = p1.get_vertex(current_vertex[0])
            # If there's no valid starting point, then the program needs to break out of the while loop, otherwise it
            # will get stuck in an infinite loop.
            else:
                break

    # If smallest_index is equal to -1, then a valid starting package was unable to be found, or after loading a few
    # packages the only ones left are invalid.
    # If that's the case then the time needs to be adjusted to validate the package(s) and allow them to be delivered.
    # I decided to add 60 minutes to the current truck's time before the program checks again since 60 minutes should
    # ensure this portion only needs to run a couple of times at most before the time makes all packages valid.
    # This works well with the program since mileage is what's being optimized and not time, so delaying other
    # packages by up to an hour isn't a large concern here. Otherwise I would want to add a minute at a time.
    #
    # As well as adding 60 minutes to the current truck's time, this section also unloads all the packages for the
    # truck being loaded. I chose to do this because it is more mileage efficient to delay all the packages by an hour
    # and try to deliver them together instead of taking the few invalid packages alone when they are validated.
    if smallest_index == -1:
        sec = 3600
        if truck_num == 1:
            time1 = time + datetime.timedelta(seconds=sec)
        elif truck_num == 2:
            time2 = time + datetime.timedelta(seconds=sec)
        for item in truck:
            hub_packages.append(item)
        truck = []

    # When the linked packages get added there's a chance that the truck might pass the randomly generated truck length,
    # which is fine, but if it surpasses 16, which is the maximum truck length, then the route needs to be thrown out
    # since that is impossible in this scenario.
    # Returning math.inf will make the miles elapsed equal to infinite, meaning the route won't be used.
    if len(truck) > 16:
        return math.inf

    # As long as the truck isn't empty, this will run.
    if len(truck) != 0:
        # Now the truck has all the packages that it will deliver, so the truck number is assigned to each package.
        for item in truck:
            p1.truck_num(item[0], truck_num)

        # After that, the time that each package will be delivered at is set, the miles elapsed is calculated and
        # the time the truck will return to the hub is calculated as well.
        info = set_delivery_times(time, miles, truck)
        miles = info[0]
        if truck_num == 1:
            time1 = info[1]
        elif truck_num == 2:
            time2 = info[1]

    # If the list of hub_packages isn't empty and if miles hasn't been set to infinite (invalidating the route),
    # then we run this again until it's empty.
    if len(hub_packages) != 0 and miles != math.inf:
        miles = algorithm(time1, time2, miles, truck_num)

    # The total miles elapsed have been kept track of so they can be returned and checked by the user.
    return miles


# Calculates the delivery time for each package as well as total miles traveled for truck.
def set_delivery_times(time, miles, truck):
    # First, the distance from the Hub to the first package on the truck is calculated
    m = d.get_weight(' HUB', p1.get_vertex(truck[0][0]))
    # Then, that distance is added to the total miles elapsed.
    miles += m
    # Then, the time taken to drive to and deliver the package is calculated. (18 mph times the distance).
    sec = round(((m / 18) * 60 * 60))
    # Then, the calculated time is added to the current time, getting the delivery time and the new current time.
    time += datetime.timedelta(seconds=sec)
    # If the package has a deadline, the program checks if that deadline has been met, throwing out the route if not.
    # (Returning miles as math.inf will make miles = infinite, which will make the route invalid).
    if truck[0][6] != 'EOD':
        t = datetime.datetime.strptime(truck[0][6][:-3], "%H:%M")
        deadline_time = datetime.timedelta(hours=t.hour, minutes=t.minute)
        if time > deadline_time:
            miles = math.inf
            return miles, time
    # Then, the delivery time is updated for the package.
    p1.delivery_time(truck[0][0], str(time))

    # This part does the same as above, but calculates the distance between the packages instead of the hub.
    for i in range(0, len(truck) - 1):
        m = d.get_weight(p1.get_vertex(truck[i][0]), p1.get_vertex(truck[i + 1][0]))
        miles += m
        sec = round(((m / 18) * 60 * 60))
        time += datetime.timedelta(seconds=sec)
        if truck[i + 1][6] != 'EOD':
            t = datetime.datetime.strptime(truck[i + 1][6][:-3], "%H:%M")
            deadline_time = datetime.timedelta(hours=t.hour, minutes=t.minute)
            if time > deadline_time:
                p1.delivery_time(truck[i + 1][0], str(time))
                miles = math.inf
                return miles, time
        p1.delivery_time(truck[i + 1][0], str(time))

    # After delivering the last package the truck has to return to the hub, so that time and mileage is calculated.
    m = d.get_weight(p1.get_vertex(truck[len(truck) - 1][0]), ' HUB')
    miles += m
    sec = ((m / 18) * 60 * 60)
    time += datetime.timedelta(seconds=sec)

    # Finally, the miles elapsed and the new current time is returned.
    return miles, time


# This method retrieves linked packages from a package with delivery instructions linking multiple packages together.
def linked_list(time, truck, current_vertex, curr_v_vertex):
    # First, a linked list, used to store packages that must be delivered together, is initialized.
    linked_list = []

    # Then, the linked packages are saved to a list from the delivery instructions.
    linked_packages = current_vertex[7][3:].split(", ")

    # After that, the linked packages are looped through, adding the package to a list of linked packages if it's still
    # in the list of hub_packages.
    for item in linked_packages:
        for item1 in hub_packages:
            if item1[0] == int(item):
                linked_list.append(hub_packages.pop(hub_packages.index(item1)))

    # After that, the linked packages have to be looped through, and any packages that they are linked to must also
    # be added to the list of linked packages.
    for package in linked_list:
        if package[7][0] == 'w':
            # Save the linked packages from delivery instructions to a list.
            linked_packages = package[7][3:].split(", ")
            # Then, the packages in that list are looped through.
            for item in linked_packages:
                # If the package is still in hub_packages, then it is saved to the list of linked packages.
                for item1 in hub_packages:
                    if item1[0] == int(item):
                        linked_list.append(hub_packages.pop(hub_packages.index(item1)))

    # Now, the list of linked packages must all be added to the truck.
    while len(linked_list) > 0:
        smallest_index = 0
        for i in range(0, len(linked_list)):
            # This part compares two packages distances from the hub. Whichever one is closest has it's
            # index saved and after all packages have been compared we have the index for the package to be
            # added to the truck.
            if d.get_weight(curr_v_vertex, p1.get_vertex(linked_list[i][0])) < \
                    d.get_weight(curr_v_vertex, p1.get_vertex(linked_list[smallest_index][0])):
                smallest_index = i

        # After all packages have been compared the closest one is popped from the hub_packages list and saved.
        current_vertex = linked_list.pop(smallest_index)
        # Then, the properly named vertex (for comparing weights between locations) is saved.
        curr_v_vertex = p1.get_vertex(current_vertex[0])
        # The closest package is added to the truck.
        truck.append(current_vertex)
        # The time that the package will leave the hub is updated.
        p1.enroute_time(current_vertex[0], str(time))

    # The truck has now been loaded with all of the linked packages, so it is returned for the rest of it to be loaded.
    return truck


# This is the main method that defines the objects used throughout the program and runs all of the methods in the
# proper order.
#
#  Press the green button in the gutter to run the script. (Auto-generated by PyCharm)
if __name__ == '__main__':
    # Imports all of the packages from the csv file and then copies all the packages into a second list.
    # The first list is the final list, which will store the best route, and the second one is for comparing to the
    # first.
    p = import_packages()
    p1 = copy.deepcopy(p)

    # Imports the table of distances from the csv file.
    d = import_distances()

    # Sets the business time to 08:00:00.
    time = datetime.timedelta(hours=8)

    # This section runs the algorithm multiple times, retrieving the total miles elapsed.
    # First, miles_least is set to infinite, so when miles_least and miles are compared for the first time, miles will
    # always be greater.
    miles_least = math.inf

    # A variable that checks to see if a good route has been saved is initialized to false.
    good_route = False

    # This will run until a satisfactory route is found (every time I've ran the program without this many times and had
    # no issues finding a satisfactory route on the first try, but this is just a safety net in case the random numbers
    # are unlucky).
    while not good_route:
        # This loop makes the algorithm run a set number of times.
        #
        # The algorithm has random elements to it, so the more times this loop runs the chances a more efficient route
        # is generated go up. I chose 20 times since 20 should get a decent route with good run time.
        for i in range(1, 20):
            # The total miles elapsed for the next route is set to 0.
            miles = 0
            # All of the items from the package hash map are copied to a list so the program can remove the routed
            # packages.
            hub_packages = []
            for item in p.map:
                hub_packages.append(item)

            # The algorithm is ran, updating the packages in p1 with the route generated.
            miles = algorithm(time, time, miles, 0)
            # If miles is less than miles_least then the algorithm found a more efficient route than the current best
            # one, so that route is saved to p and miles_least is updated.
            if miles < miles_least:
                p = copy.deepcopy(p1)
                miles_least = miles
        # After the loop is done running the most efficient route has been saved and miles_least is rounded to the first
        # decimal place since sometimes a number like 124.5999999999998 is saved.
        miles_least = round(miles_least, 2)

        # With this data set, under 140 miles is considered well-optimized, so this check makes sure the best route is
        # under 140 miles, looping another 20 times if it isn't (as mentioned above I never had a scenario where this
        # was needed, but it's a good safety net in case of bad luck the first loop).
        if miles_least < 140:
            good_route = True

    # A notification stating that the route has been generated is printed before the program runs the main_menu().
    print('Route Generated')

    # Starts the main menu for user input.
    main_menu(time, miles_least)