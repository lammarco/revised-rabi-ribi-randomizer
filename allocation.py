import random, bisect
from utility import is_egg, print_ln

class Allocation(object):
    # Attributes:
    #
    # list: items_to_allocate
    #
    # dict: item_at_item_location  (item location -> item at item location)
    #
    # dict: outgoing_edges  [location -> list(Edge)]
    # dict: incoming_edges  [location -> list(Edge)]
    # list: edges  [list(Edge)]   <-- indexed by edge_id
    #
    # list: walking_left_transitions  (MapTransition objects)
    #
    # dict: edge_replacements  [(from_location, to_location) -> template_changes]
    # list: map_modifications  (Paths to diff files)

    def __init__(self, data, settings):
        self.items_to_allocate = list(data.items_to_allocate)
        self.walking_left_transitions = list(data.walking_left_transitions)


    def shuffle(self, data, settings):
        self.map_modifications = list(data.default_map_modifications)

        # Shuffle Items
        self.allocate_items(data, settings)

        # Shuffle Constraints
        self.choose_constraint_templates(data, settings)

        # Shuffle Locations
        self.construct_graph(data, settings)

        # Shuffle Start Location
        if settings.shuffle_start_location:
            index = random.randrange(sum(l.weight for l in data.start_locations))
            for current_location in data.start_locations:
                if index < current_location.weight: break
                index -= current_location.weight
            self.start_location = current_location
        else:
            self.start_location = data.start_locations[0]
            self.start_location.location = "FOREST_START"
    def allocate_items(self, data, settings):
        item_slots = data.item_slots

        #if not settings.shuffle_items:
            #self.item_at_item_location = dict(zip(item_slots, item_slots))
            #return

        random.shuffle(self.items_to_allocate)

        # A map of location -> item at location
        self.item_at_item_location = dict(zip(item_slots, self.items_to_allocate))
        self.item_at_item_location.update(data.unshuffled_allocations)

    def choose_constraint_templates(self, data, settings):
        self.edge_replacements = {}

        def get_template_count(settings):
            low = int(0.5 * settings.constraint_changes)
            high = int(1.5 * settings.constraint_changes + 2)
            if settings.constraint_changes <= 0:
                high = 0
            if settings.min_constraint_changes >= 0:
                low = int(settings.min_constraint_changes)
            if settings.max_constraint_changes >= 0:
                high = int(settings.max_constraint_changes + 1)
            if low == high:return low
            return random.randrange(low, high)

        templates = dict()
        orig_templates = list(data.template_constraints)
        for t in orig_templates:
            templates[t.name] = t
        target_template_count = get_template_count(settings)

        picked_templates = []
        update_table = True
        template_weights = [0 for j in range(len(templates))]
        template_names = ["" for j in range(len(templates))]
        template_index = {}
        while len(templates) > 0 and len(picked_templates) < target_template_count:
            if update_table:
                update_table = False
                i = 0
                total_weight = 0
                removed_wiehgt = 0
                template_index.clear()
                for t in templates:
                    total_weight += templates[t].weight
                    template_names[i] = templates[t].name
                    template_weights[i] = total_weight
                    template_index[templates[t].name] = i
                    i += 1
                template_weights = template_weights[:i]

            while True:
                index = random.randrange(total_weight)
                picked = bisect.bisect(template_weights, index)
                current_template = template_names[picked]
                if current_template[0] != '!':
                    break

            picked_templates.append(templates[current_template])
            
            # remove all conflicting templates
            for conflict in templates[current_template].conflicts_names:
                if conflict in templates:
                    removed_wiehgt += templates[conflict].weight
                    remove_index = template_index[templates[conflict].name]
                    template_names[remove_index] = "!"
                    del templates[conflict]

            if (removed_wiehgt / total_weight) > 0.35:
                update_table = True


        self.picked_templates = picked_templates
        for template in picked_templates:
            for change in template.changes:
                self.edge_replacements[(change.from_location, change.to_location)] = change
            self.map_modifications.append(template.template_file)

    def construct_graph(self, data, settings):
        edges = list(data.initial_edges)
        edge_id = data.replacement_edges_id
        originalNEdges = edge_id
        outgoing_edges = dict((key, list(edge_ids)) for key, edge_ids in data.initial_outgoing_edges.items())
        incoming_edges = dict((key, list(edge_ids)) for key, edge_ids in data.initial_incoming_edges.items())

        # Edge Constraints
        edge_replacements = self.edge_replacements
        for original_constraint in data.edge_constraints:
            key = (original_constraint.from_location, original_constraint.to_location)
            if key in edge_replacements:
                constraint = edge_replacements[key]
            else:
                constraint = original_constraint
            edges[edge_id].satisfied = constraint.prereq_lambda
            edge_id += 1

        # Map Transitions
        if settings.shuffle_map_transitions:
            random.shuffle(self.walking_left_transitions)

            edge_id = data.transition_edges_id
            for ltr in self.walking_left_transitions:
                edges[edge_id].to_location = ltr.origin_location
                edges[edge_id+1].from_location = ltr.origin_location
                edge_id += 2

        for edge in edges[originalNEdges:]:
            outgoing_edges[edge.from_location].append(edge.edge_id)
            incoming_edges[edge.to_location].append(edge.edge_id)

        self.edges = edges
        self.outgoing_edges = outgoing_edges
        self.incoming_edges = incoming_edges


    def shift_eggs_to_hard_to_reach(self, data, settings, reachable_items, hard_to_reach_items):
        reachable_items = set(reachable_items)

        hard_to_reach_pairs = [(item_location, item_name)
                        for item_location, item_name in self.item_at_item_location.items()
                        if item_name in hard_to_reach_items]

        hard_to_reach_eggs = [(item_location, item_name) for item_location, item_name in hard_to_reach_pairs
                        if is_egg(item_name)]
        hard_to_reach_non_eggs = [(item_location, item_name) for item_location, item_name in hard_to_reach_pairs
                        if not is_egg(item_name)]

        non_hard_to_reach_eggs = [(item_location, item_name)
                        for item_location, item_name in self.item_at_item_location.items()
                        if is_egg(item_name) and item_name not in hard_to_reach_items and item_name in reachable_items]

        hard_to_reach_eggs.sort(key=lambda p:p[0])
        hard_to_reach_non_eggs.sort(key=lambda p:p[0])
        non_hard_to_reach_eggs.sort(key=lambda p:p[0])

        n_eggs_in_map = data.nHardToReach + settings.extra_eggs
        if len(non_hard_to_reach_eggs) + len(hard_to_reach_eggs) < n_eggs_in_map:
            # Not enough reachable eggs. Retry.
            return False, None
        remainingEggsToPlace = random.sample(non_hard_to_reach_eggs, n_eggs_in_map - len(hard_to_reach_eggs))
        random.shuffle(remainingEggsToPlace)

        extra_eggs = remainingEggsToPlace[:settings.extra_eggs]
        eggs_to_move = remainingEggsToPlace[settings.extra_eggs:]
        assert len(eggs_to_move) == len(hard_to_reach_non_eggs)

        for item_location, item_name in self.item_at_item_location.items():
            if is_egg(item_name):
                self.item_at_item_location[item_location] = None

        for item_location, item_name in hard_to_reach_eggs:
            self.item_at_item_location[item_location] = item_name

        for item_location, item_name in extra_eggs:
            self.item_at_item_location[item_location] = item_name

        for z1, z2 in zip(hard_to_reach_non_eggs, eggs_to_move):
            # Swap
            item_location_1, item_name_1 = z1
            item_location_2, item_name_2 = z2
            self.item_at_item_location[item_location_1] = item_name_2
            self.item_at_item_location[item_location_2] = item_name_1

        # Verification
        actual_n_eggs = sum(1 for item_location, item_name in self.item_at_item_location.items() if is_egg(item_name))
        assert n_eggs_in_map == actual_n_eggs

        goal_eggs = [item_name for item_location, item_name in (eggs_to_move + hard_to_reach_eggs)]

        return True, goal_eggs

    def print_important_item_locations(self):
        # DEBUG CODE FOR FINDING ITEMS
        print_ln('--Item Locations--')
        for k,v in self.item_at_item_location.items():
            if v in ('PIKO_HAMMER','WALL_JUMP','RABI_SLIPPERS','AIR_JUMP','AIR_DASH','BUNNY_WHIRL','HAMMER_ROLL','SLIDING_POWDER','CARROT_BOMB','CARROT_SHOOTER','FIRE_ORB','WATER_ORB','BUNNY_STRIKE','BUNNY_AMULET','SPEED_BOOST'):
                print_ln('%s @ %s' % (v, k))

        print_ln('--Modified Constraints--')
        print_ln('\n'.join(t.name for t in self.picked_templates))

    def count_eggs(self):
        return sum(1 for item_name in self.item_at_item_location.values() if is_egg(item_name))


