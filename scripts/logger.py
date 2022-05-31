from datetime import datetime

class SubGoalManager:
    subgoal1: bool = False
    subgoal2: bool = False
    subgoal3: bool = False
    current_subgoal: int = 1

    def reset(self):
        self.current_subgoal = 1
        self.subgoal1 = False
        self.subgoal2 = False
        self.subgoal3 = False

    def print_status(self, status):
        return u'\u2713' if status else '?'

    def print_conclusion(self):
        if self.current_subgoal < 4:
            return f"Proving subgoal C{self.current_subgoal}..."
        else:
            return  "Done.                                     "

    def getInfo(self):
        if self.current_subgoal > 0:
            msg = f"SubgoalC1: {self.print_status(self.subgoal1)} "
        if self.current_subgoal > 1:
            msg += f"SubgoalC2: {self.print_status(self.subgoal2)} "
        if self.current_subgoal > 2:
             msg += f"SubgoalC3: {self.print_status(self.subgoal3)} "
        msg += f"> {self.print_conclusion()}"
        return msg

    def update_status(self, id, status):
        if id == 1:
            self.subgoal1 = status
        elif id == 2:
            self.subgoal2 = status
        else:
            self.subgoal3 = status

SGM = SubGoalManager()

class Logger:

    msg: str = ""
    # iteration
    cases: int = 0

    def __init__(self) -> None:
        pass

    def info(self, src, msg, end="\n") -> None:
        print(f"INFO: [{src}] {msg}", end=end, flush=True)

    # ==============================================================================================

    def run_start(self, cases: int, start_time):
        self.start_time = start_time
        self.cases == cases
        self.info("prover", start_time.strftime('Starting at %H:%M:%S'))

    def begin_proving_round(self, round_id):
        print("\n\n================================ Testcase {:02d} ==================================".format(round_id))
        SGM.reset()
    
    def print_stat(self):
        msg = SGM.getInfo()
        print(f"{msg}", end = "\r", flush=True)

    def finish(self):
        print("\n\n=================================== End ======================================")

LOGGER = Logger()
