from allocation import Allocation
from analyzer import Analyzer
from difficultyanalysis import DifficultyAnalysis
from utility import fail, print_ln
import time, random

class Generator(object):
    def __init__(self, data, settings):
        self.data = data
        self.settings = settings
        self.allocation = Allocation(data, settings)

    def generate_seed(self, seed):
        if seed != None:
            random.seed(seed)
        else:
            state = random.getstate()[1]
            seed = state[2] ^ (state[4] << 32) ^ (state[6] << 64) ^ (state[8] << 96)
            random.seed(seed)

        SEED_UPDATE_ATTEMPTS = 1000
        MAX_ATTEMPTS = self.settings.max_attempts
        success = False
        skip_difficulty_analysis = (self.settings.min_difficulty <= 0 and self.settings.max_sequence_breakability == None)

        start_time = time.time()
        for attempts in range(MAX_ATTEMPTS):
            self.shuffle()
            self.allocation.enable_swaps(True)
            analyzer = Analyzer(self.data, self.settings, self.allocation)
            self.allocation.enable_swaps(False)
            if analyzer.success:
                if not self.settings.egg_goals:
                    success = True
                else:
                    shift_success, goal_eggs = self.shift_eggs_to_hard_to_reach(analyzer.reachable, analyzer.hard_to_reach_items)
                    if shift_success:
                        analyzer = Analyzer(self.data, self.settings, self.allocation, goals=goal_eggs)
                        if analyzer.success:
                            success = True

            if success:
                difficulty_analysis = None
                if not skip_difficulty_analysis:
                    # Run difficulty analysis
                    if self.settings.egg_goals: goals = analyzer.goals
                    else: goals = analyzer.hard_to_reach_items
                    difficulty_analysis = DifficultyAnalysis(self.data, analyzer, goals)

                if self.settings.min_difficulty > 0:
                    if difficulty_analysis.difficulty_score < self.settings.min_difficulty:
                        success = False

                if self.settings.max_sequence_breakability != None:
                    if difficulty_analysis.breakability_score > self.settings.max_sequence_breakability:
                        success = False

            if success:
                if skip_difficulty_analysis:
                    # Run difficulty analysis
                    if self.settings.egg_goals: goals = analyzer.goals
                    else: goals = analyzer.hard_to_reach_items
                    difficulty_analysis = DifficultyAnalysis(self.data, analyzer, goals)
                break
            self.allocation.revert_graph(self.data)
            if (attempts + 1) % SEED_UPDATE_ATTEMPTS == 0:
                state = random.getstate()[1]
                seed = seed ^ state[2] ^ (state[4] << 32) ^ (state[6] << 64) ^ (state[8] << 96)
                self.allocation = Allocation(self.data, self.settings)
                random.seed(seed)

        time_taken = time.time() - start_time
        time_string = '%.2f seconds' % (time_taken)

        if not success:
            fail('Unable to generate a valid seed after %d attempts in %s (%.2f/sec)' % (MAX_ATTEMPTS, time_string, MAX_ATTEMPTS / time_taken))

        print_ln('Seed generated after %d attempts in %s (%.2f/sec)' % (attempts+1, time_string, (attempts + 1) / time_taken))
        # Generate Visualization and Print Output:
        if self.settings.debug_visualize:
            Analyzer(self.data, self.settings, self.allocation, visualize=True)
            #self.allocation.print_important_item_locations()

        return self.allocation, analyzer, difficulty_analysis, seed

    def shuffle(self):
        self.allocation.shuffle(self.data, self.settings)

    def shift_eggs_to_hard_to_reach(self, reachable_items, hard_to_reach_items):
        return self.allocation.shift_eggs_to_hard_to_reach(self.data, self.settings, reachable_items, hard_to_reach_items)

