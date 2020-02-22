# Title: Leon's blackjack bookmaker
# (c) 2020 Leon S. Erikson
# Licensed to others under BSD3


import random
import sys
import pickle
import tkinter as tk
from tkinter import messagebox
from tkinter import filedialog
from math import floor


# DEBUG STUFF

# DEBUG levels:
# 1 : non-pair info
# 2 : split info

DEBUG = 0

# Simulator constants used for pair hand EV calculation.
SIM_MAX = 10 ** 7

# Useful global constants
BLACKJACK_PAY = {True: 3/2, False: 6/5}

HARD_HAND_COMP = {21:[(1, 10)],
                  20:[(10,10)],
                  19:[(9,10)],
                  18:[(8,10),(9,9)],
                  17:[(7,10),(8,9)],
                  16:[(6,10),(7,9),(8,8)],
                  15:[(5,10),(6,9),(7,8)],
                  14:[(4,10),(5,9),(6,8),(7,7)],
                  13:[(3,10),(4,9),(5,8),(6,7)],
                  12:[(2,10),(3,9),(4,8),(5,7),(6,6)],
                  11:[(2,9),(3,8),(4,7),(5,6)],
                  10:[(2,8),(3,7),(4,6),(5,5)],
                  9:[(2,7),(3,6),(4,5)],
                  8:[(2,6),(3,5),(4,4)],
                  7:[(2,5),(3,4)],
                  6:[(2,4),(3,3)],
                  5:[(2,3)],
                  4:[(2,2)]
                  }

ONE_DECK = [2, 2, 2, 2,
            3, 3, 3, 3,
            4, 4, 4, 4,
            5, 5, 5, 5,
            6, 6, 6, 6,
            7, 7, 7, 7,
            8, 8, 8, 8,
            9, 9, 9, 9,
            10, 10, 10, 10,
            10, 10, 10, 10,
            10, 10, 10, 10,
            10, 10, 10, 10,
            1, 1, 1, 1,
            ]
ONE_DECK_DIST = {1: 0.07692307692307693,
                 2: 0.07692307692307693,
                 3: 0.07692307692307693,
                 4: 0.07692307692307693,
                 5: 0.07692307692307693,
                 6: 0.07692307692307693,
                 7: 0.07692307692307693,
                 8: 0.07692307692307693,
                 9: 0.07692307692307693,
                 10: 0.3076923076923077
                 }

CARD_VALUES = [2, 3, 4, 5, 6, 7, 8, 9, 10, 1]

        
COLORS = {'H':'pale green',
          'D':'lime green',
          'S':'red',
          'P':'deep sky blue',
          '?':'gray'
          }

DEVIATION_COLOR = 'hot pink'

EV_INDEX = {'S':0, 'H':1, 'D':2, 'P':3}

REV_EV_INDEX = {0:'S', 1:'H', 2:'D', 3:'P'}

NUM_TO_TEXT = {1:'A', 2:'2', 3:'3', 4:'4', 5:'5', 6:'6',
              7:'7', 8:'8', 9:'9', 10:'T', 11:'A'}

#   Terminology
#   fpc: first player card
#   spc: second player card
#   duc: dealer up card
#   ddc: dealer down card
#   pht: player hand total
#   dht: dealer hand total
#   'card', is just a single number 1 - 10, representing the numeric value of
#   a playing card. 1's are aces.
#   EV, is expected value. The average return, from a one unit base bet,
#   over time.

#   Book contains the best play for a given player hand and dealer up card.
#   The book keys for plays and EVs are in the format: (fpc, spc, duc), with
#   the constraint that the fpc, if not equal to the spc, always has a lower
#   value than the spc. The book values are in the format:
#   [play, stand EV, hit EV, double EV, split EV (for pairs only)], with
#   plays being one of 'S' for stand, 'H' for hit, 'D' for double, and
#   'P' for split.

book = {}

# The application class
class Book(tk.Frame):
    """GUI application for custom deck play book and EV creation."""
    button_states = {True:'sunken', False:'raised'}

    
    def __init__(self, parent):
        """Initialize the frame."""
        super(Book, self).__init__(parent)
        self.parent = parent
        # self.deck_choice is one of 'infinite', 'finite', or 'custom
        self.deck_choice = 'infinite'
        # self.got_book is one of 'waiting', 'building', or 'finished'
        self.got_book = "waiting"
        self.num_decks = 1
        self.deck = ONE_DECK.copy()
        self.play_deviations = {}
        self.create_menus()
        
        self.show_frame = tk.Frame(self.parent, bd=0)
        self.show_frame.pack(expand=True, fill='both')
        
        self.playlist_stringvars = []
        self.playlist_labels = []
        for label_index in range(0, 280):
            play_var = tk.StringVar()
            self.playlist_stringvars.append(play_var)
            play_label = tk.Label(self.show_frame, textvariable = play_var, 
                                  font = (None, 15))
            play_label.bind(
                    "<Button-1>",
                    lambda e, label_index= \
                        label_index:self.set_play_deviation(label_index))
            self.playlist_labels.append(play_label)

        self.game_rules_Text = tk.Text(self.show_frame, height=17, width=30)
        self.game_rules_Text.place(x=0, y=0)

        self.game_stats_Text = tk.Text(self.show_frame, height=3, width=30)
        self.game_stats_Text.place(x=0, y=240)

        self.game_status_Text = tk.Text(self.show_frame, height=4, width=30)
        self.game_status_Text.place(x=0, y=290)
        
        self.initialize_show_frame()
        self.show_game_info()
        self.update_book_build_status()
    
    def create_menus(self):
        """create main window menus."""
        self.menu = tk.Menu(self.parent)
        self.parent.config(menu=self.menu)

        self.menu_book = tk.Menu(self.menu, tearoff=0)
        self.menu_book.add_command(label="Load book", command=self.load)
        self.menu_book.add_command(label="Save book", command=self.save)
        self.menu_book.add_command(label="Build book", command=self.build)
        self.menu_book.add_command(label="Build pairs",
                                   command=self.all_pair_redo)        
        self.menu_book.entryconfig("Save book", state="disabled")
        self.menu_book.entryconfig("Build pairs", state="disabled")  
        
        self.menu.add_cascade(label="Book", menu=self.menu_book)

        self.menu_rules = tk.Menu(self.menu, tearoff=0)
        

        self.deck_choice_stringvar = tk.StringVar(None, 'infinite')
                   
        self.menu_rules.add_radiobutton(
                label="Infinite Deck",
                variable=self.deck_choice_stringvar,
                value='infinite',
                command=self.set_deck_infinite
                )
        self.menu_rules.add_radiobutton(
                label="Finite Deck",
                variable=self.deck_choice_stringvar,
                value='finite',
                command=self.set_deck_finite
                )
        self.menu_rules.add_radiobutton(
                label="Custom Deck",
                variable=self.deck_choice_stringvar,
                value='custom',
                command=self.set_deck_custom
                )
        self.menu_rules.add_separator()
        
        self.double_var = tk.StringVar(None, "first two")
        self.menu_rules.add_radiobutton(
                label="Double Anytime",
                variable=self.double_var,
                value='any hand',
                command=lambda: self.toggle('any hand')
                )
        self.menu_rules.add_radiobutton(
                label="Double First Two Cards",
                variable=self.double_var,
                value='first two',
                command=lambda: self.toggle('first two')
                )
        self.menu_rules.add_radiobutton(
                label="Double Hard 9, 10, 11 Only",
                variable=self.double_var,
                value='9 10 11',
                command=lambda: self.toggle('9 10 11')
                )
        self.menu_rules.add_radiobutton(
                label="Double Hard 10, 11 Only",
                variable=self.double_var,
                value='10 11',
                command=lambda: self.toggle('10 11')
                )
        self.menu_rules.add_separator()
        
        self.fullpay_var = tk.BooleanVar(None, True)
        self.menu_rules.add_radiobutton(
                label="BJ Pays 3:2",
                variable=self.fullpay_var,
                value=True,
                command=lambda: self.toggle('PAY full')
                )
        self.menu_rules.add_radiobutton(
                label="BJ Pays 6:5",
                variable=self.fullpay_var,
                value=False,
                command=lambda: self.toggle('PAY less')
                )
        self.menu_rules.add_separator()
        
        self.msh_var = tk.IntVar(None, 4)
        self.menu_rules.add_radiobutton(
                label="Max Split Hands = 4",
                variable=self.msh_var,
                value=4,
                command=lambda: self.toggle('msh4')
                )
        self.menu_rules.add_radiobutton(
                label="Max Split Hands = 3",
                variable=self.msh_var,
                value=3,
                command=lambda: self.toggle('msh3')
                )
        self.menu_rules.add_radiobutton(
                label="Max Split Hands = 2",
                variable=self.msh_var,
                value=2,
                command=lambda: self.toggle('msh2')
                )
        self.menu_rules.add_separator()
        self.dhs17_var = tk.BooleanVar(None, True)
        self.menu_rules.add_checkbutton(
                label="DHS17",
                variable=self.dhs17_var,
                command=lambda: self.toggle('DHS17')
                )
        self.das_var = tk.BooleanVar(None, True)
        self.menu_rules.add_checkbutton(
                label="DAS",
                variable=self.das_var,
                command=lambda: self.toggle('DAS')
                )
        self.hsa_var = tk.BooleanVar(None, False)
        self.menu_rules.add_checkbutton(
                label="HSA",
                variable=self.hsa_var,
                command=lambda: self.toggle('HSA')
                )
        self.rsa_var = tk.BooleanVar(None, True)
        self.menu_rules.add_checkbutton(
                label="RSA",
                variable=self.rsa_var,
                command=lambda: self.toggle('RSA')
                )
        self.menu.add_cascade(label="Rules", menu=self.menu_rules)
        self.menu_player = tk.Menu(self.menu, tearoff=0)
        self.tem_var = tk.BooleanVar(None, False)
        self.menu_player.add_checkbutton(
                label="Take Even Money",
                variable=self.tem_var,
                command=lambda: self.toggle('TEM')
                )
        self.ti_var = tk.BooleanVar(None, False)
        self.menu_player.add_checkbutton(
                label="Take Insurance",
                variable=self.ti_var,
                command=lambda: self.toggle('TI')
                )
        self.menu.add_cascade(label="Player", menu=self.menu_player)
        self.menu_detail = tk.Menu(self.menu, tearoff=0)
        self.menu_detail.add_command(
                label="Show all play EVs", 
                command=self.print_ev
                )
        self.menu_detail.add_command(
                label="Show hard hand deviations",
                command=self.show_play_deviations
                )
        self.menu.add_cascade(label="Details", menu=self.menu_detail)
        self.menu.entryconfig("Details", state="disabled")
        self.menu_help = tk.Menu(self.menu, tearoff=0)
        self.menu_help.add_command(label="Instructions", command=self.help)
        self.menu.add_cascade(label="Help", menu=self.menu_help)
            
    def help(self):
        help_message_lines = [
             'Welcome! To create a play book, first select your desired deck.',
             'Decks can be infinite, finite with a specified number of decks,',
             'or custom allowing you to specify deck composition by number of',
             'cards. Then select your desired game rules: DHS17 for dealer ',
             'hits soft 17, DAS for double after split, HSA for player may ',
             'hit split aces, and RSA for player may resplit aces up to the ',
             'max ace split amount. Once your desired rules are set, click ',
             'the book menu and select "build book."']
        messagebox.showinfo('Instructions', " ".join(help_message_lines)) 
                        
    def save(self):
        """Save a 'book' after one has been built."""
        book_filename = filedialog.asksaveasfilename(
                title="Save File",
                filetypes=(("Book Files", "*.book"),
                ("All files", "*.*"))
                )
        if book_filename is None or book_filename == '':
            return
        f = open(book_filename, "wb")
        pickle.dump(book, f)

    def load(self):
        """Load a book after one has been saved."""
        global book
        book = {}
        book_filename = filedialog.askopenfilename(
                title="Open File",
                filetypes=(("Book Files", "*.book"),
                ("All files", "*.*"))
                )
        if book_filename is None or book_filename == '':
            return
        
        f = open(book_filename, "rb")
        book = pickle.load(f)

        self.reset_plays()

        self.deck = book['book_deck']
        loaded_rules = book['rules']

        assert loaded_rules[0] in ['infinite', 'finite', 'custom']
        self.deck_choice = loaded_rules[0]
        self.deck_choice_stringvar.set(loaded_rules[0])
        
        if self.dhs17_var.get() != loaded_rules[1]:
            self.toggle('DHS17')
            self.dhs17_var.set(loaded_rules[1])

        if self.das_var.get() != loaded_rules[2]:
            self.toggle('DAS')
            self.das_var.set(loaded_rules[2])

        if self.hsa_var.get() != loaded_rules[3]:
            self.toggle('HSA')
            self.hsa_var.set(loaded_rules[3])

        if self.rsa_var.get() != loaded_rules[4]:
            self.toggle('RSA')
            self.rsa_var.set(loaded_rules[4])

        if self.fullpay_var.get() != loaded_rules[5]:
            if loaded_rules[5] == True:
                self.toggle('PAY full')
                self.fullpay_var.set(1)
            else:
                self.toggle('PAY less')
                self.fullpay_var.set(0)
            
        if self.msh_var.get() != loaded_rules[6]:
            if loaded_rules[6] == 2:
                self.toggle('msh2')
                self.msh_var.set(2)
            elif loaded_rules[6] == 3:
                self.toggle('msh3')
                self.msh_var.set(3)
            else:
                self.toggle('msh4')
                self.msh_var.set(4)

        if self.double_var.get() != loaded_rules[7]:
            self.toggle(loaded_rules[7])
            self.double_var.set(loaded_rules[7])

        assert type(loaded_rules[8]) == int
        self.num_decks = loaded_rules[8]
        self.menu.entryconfig("Details", state="normal")
        self.menu_book.entryconfig("Save book", state="normal")
        self.menu_book.entryconfig("Build pairs", state="normal")

        for index in range(0, len(self.playlist_stringvars)):
            self.playlist_stringvars[index].set('?')
            self.playlist_labels[index].config(bg='gray')
        self.show_frame.update()

        for index in range(0, len(self.playlist_stringvars)):
            book_tuple = self.get_book_tuple_from_playlist_index(index)
            if book_tuple[1] == 'hard':
                play, _ = self.hard_hand_book_lookup(
                        book_tuple[0], book_tuple[2])
            elif book_tuple[1] == 'soft':
                play, _ = self.book_lookup(
                        [1, book_tuple[0] - 11], book_tuple[2])
            else:
                play, _ = self.book_lookup(
                        [book_tuple[0], book_tuple[0]],
                        book_tuple[2])

            assert play in ['S', 'H', 'D', 'P']
            self.playlist_stringvars[index].set(play)
            self.playlist_labels[index].config(bg=COLORS[play])
            self.show_frame.update()
        self.got_book = "finished"
        self.update_book_build_status()
        self.show_game_info()
           
    def update_book_build_status(self, card_list=None, hand_type=None):
        """Update the game status info shown in the main window."""
        self.game_status_text = "BOOK STATUS:\n"
        if self.got_book == "building":
            self.game_status_text += 'Book is being built. \nWorking on '
            self.game_status_text += hand_type + ' hand: \n'
            self.game_status_text += '(' + NUM_TO_TEXT[card_list[0]] + ', ' + \
                                        NUM_TO_TEXT[card_list[1]] + ', ' + \
                                        NUM_TO_TEXT[card_list[2]] + ')'
        elif self.got_book == "waiting":
            self.game_status_text += 'Load or build a book under ' + \
                                     '\nthe book menu to get started.'
        elif self.got_book == "finished":
            self.game_status_text += \
                'Built. Left click a play to\nset a play deviation.'

        self.game_status_Text.delete('1.0', tk.END)
        self.game_status_Text.insert('1.0', self.game_status_text)
        self.game_status_Text.update()

    def reset_plays(self, type='all'):
        """Reset either all plays or just pair plays in the main window."""
        if type == 'all':
            start_index = 0
            self.menu_book.entryconfig("Build pairs", state="disabled")
        elif type == 'pair':
            start_index = 180
        end_index = len(self.playlist_stringvars)
        self.got_book = "waiting"
        self.menu.entryconfig("Details", state="disabled")
        self.menu_book.entryconfig("Save book", state="disabled")
            
        for index in range(start_index, end_index):
            self.playlist_stringvars[index].set('?')
            self.playlist_labels[index].config(bg='gray')
        self.update_book_build_status()
        self.show_frame.update()

    def set_play_deviation(self, label_index):
        """Sets a play deviation."""
        hand_total, hand_type, duc = \
            self.get_book_tuple_from_playlist_index(label_index)
        assert hand_type in ['hard', 'soft', 'pair']
        if hand_type == 'hard':
            book_play, _ = self.hard_hand_book_lookup(hand_total, duc)
        elif hand_type == 'soft':
            book_play, _ = self.book_lookup([1, hand_total - 11], duc)
        else:
            book_play, _ = self.book_lookup([int(hand_total / 2),
                                     int(hand_total / 2)],
                                    duc)
        if hand_type == 'pair':
            plays = ['S', 'H', 'D', 'P']
        else:
            plays = ['S', 'H', 'D']

        display_play = self.playlist_stringvars[label_index].get()
        play_index = plays.index(display_play)
        play_index += 1
        if play_index == len(plays):
            play_index -= len(plays)
        new_play = plays[play_index]
        self.playlist_stringvars[label_index].set(new_play)
        if new_play == book_play:
            self.playlist_labels[label_index].config(bg=COLORS[new_play])
        else:
            self.playlist_labels[label_index].config(bg=DEVIATION_COLOR)
        self.show_game_info()
                   
    def build(self):
        """Builds the book for the current rule set."""
        self.reset_plays()
        self.got_book = "building"
        current_rules = [
                self.deck_choice, 
                self.dhs17_var.get(), 
                self.das_var.get(),
                self.hsa_var.get(), 
                self.rsa_var.get(), 
                self.fullpay_var.get(),
                self.msh_var.get(), 
                self.double_var.get(), 
                self.num_decks
                ]
        self.show_game_info()
        global book
        book = {}
        book['book_deck'] = self.deck 
        book['rules'] = current_rules

        for pht in range(21, 10, -1):
            for duc_11 in range(2, 12):
                for cards in HARD_HAND_COMP[pht]:
                    if duc_11 == 11:
                        duc = 1
                    else:
                        duc = duc_11
                    self.update_book_build_status(
                            [cards[0], cards[1], duc], 
                            'hard'
                            )
                    self.hand_builder(cards[0], cards[1], duc, self.deck)
                if pht >= 8 and pht <= 17:
                    play, _ = self.hard_hand_book_lookup(pht, duc)
                    play = self.double_check(play, cards, duc)
                    label_index = self.get_playlist_index_from_book_tuple(
                            pht, 'hard', duc)
                    self.playlist_stringvars[label_index].set(play)
                    self.playlist_labels[label_index].config(bg=COLORS[play])
                    self.show_frame.update()
    
        for phs in range(21, 11, -1):
            for duc_11 in range(2, 12):
                if duc_11 == 11:
                    duc = 1
                else:
                    duc = duc_11
                self.update_book_build_status([1, phs - 11, duc], 'soft')
                self.hand_builder(1, phs - 11, duc, self.deck)
                if phs >= 13 and phs <= 20:
                    play, _ = self.book_lookup([1, phs - 11], duc)
                    play = self.double_check(play, [1, phs - 11], duc)
                    label_index = self.get_playlist_index_from_book_tuple(
                            phs, 'soft', duc)
                    self.playlist_stringvars[label_index].set(play)
                    self.playlist_labels[label_index].config(bg=COLORS[play])
                    self.show_frame.update()
    
        for pht in range(10, 3, -1):
            for duc_11 in range(2, 12):
                if duc_11 == 11:
                    duc = 1
                else:
                    duc = duc_11
                for cards in HARD_HAND_COMP[pht]:
                    self.update_book_build_status(
                            [cards[0], cards[1], duc], 
                            'hard'
                            )
                    self.hand_builder(cards[0], cards[1], duc, self.deck)
                if pht >= 8 and pht <= 20:
                    play, _ = self.hard_hand_book_lookup(pht, duc)
                    play = self.double_check(play, cards, duc)
                    label_index = self.get_playlist_index_from_book_tuple(
                            pht, 'hard', duc)
                    self.playlist_stringvars[label_index].set(play)
                    self.playlist_labels[label_index].config(bg=COLORS[play])
                    self.show_frame.update()
                    
        for pair_of_11 in range(11, 1, -1):
            if pair_of_11 == 11:
                pair_of = 1
            else:
                pair_of = pair_of_11
            for duc_11 in range(2, 12):
                if duc_11 == 11:
                    duc = 1
                else:
                    duc = duc_11
                self.update_book_build_status(
                        [pair_of, pair_of, duc], 
                        'pair'
                        )
                self.pair_hand_builder(pair_of, duc, self.deck)
                play, _ = self.book_lookup([pair_of, pair_of], duc)
                label_index = self.get_playlist_index_from_book_tuple(
                        pair_of, 'pair', duc)
                self.playlist_stringvars[label_index].set(play)
                self.playlist_labels[label_index].config(bg=COLORS[play])
                self.show_frame.update()
        
        self.menu.entryconfig("Details", state="normal")
        self.menu_book.entryconfig("Save book", state="normal")
        self.menu_book.entryconfig("Build pairs", state="normal")
        self.got_book = "finished"
        self.update_book_build_status()
        self.show_game_info()

    def all_pair_redo(self):
        """Re-builds all pair hands."""
        self.reset_plays('pair')
        self.got_book = "building"
        self.show_game_info()
        for pair_of_11 in range(11, 1, -1):
            if pair_of_11 == 11:
                pair_of = 1
            else:
                pair_of = pair_of_11
            for duc_11 in range(2, 12):
                if duc_11 == 11:
                    duc = 1
                else:
                    duc = duc_11
                self.update_book_build_status([pair_of, pair_of, duc], 'pair')
                self.pair_hand_builder(pair_of, duc, self.deck)
                play, _ = self.book_lookup([pair_of, pair_of], duc)
                label_index = self.get_playlist_index_from_book_tuple(
                        pair_of, 'pair', duc)
                self.playlist_stringvars[label_index].set(play)
                self.playlist_labels[label_index].config(bg=COLORS[play])
                self.show_frame.update()
        self.menu.entryconfig("Details", state="normal")
        self.menu_book.entryconfig("Save book", state="normal")
        self.got_book = "finished"
        self.update_book_build_status()
        self.show_game_info()

    def show_game_info(self):
        """Creates the game info text for the main window."""
        self.game_rules_text = "GAME RULES/ PLAYER CHOICES:"
        if self.fullpay_var.get():
            self.game_rules_text += "\nBlackjack pays 3:2"
        else:
            self.game_rules_text += "\nBlackjack pays 6:5"
        self.game_rules_text += "\nDeck choice: " + str(self.deck_choice)
        if self.deck_choice == 'finite':
            self.game_rules_text += "\nNumber of decks = " + \
                    str(self.num_decks)
        elif self.deck_choice == 'custom':
            self.game_rules_text += "\nDeck composition: \n"
            for card in CARD_VALUES:
                card_text = NUM_TO_TEXT[card]
                self.game_rules_text += card_text + ":" + \
                    str(self.deck.count(card)) + ", "
        self.game_rules_text += "\nDouble on: " + self.double_var.get()
        self.game_rules_text += "\nDHS17: " + str(self.dhs17_var.get())
        self.game_rules_text += "\nMax Split Hands: " + str(self.msh_var.get())
        self.game_rules_text += "\nDAS: " + str(self.das_var.get())
        self.game_rules_text += "\nRSA: " + str(self.rsa_var.get())
        self.game_rules_text += "\nHSA: " + str(self.hsa_var.get())
        self.game_rules_text += "\nTake even money: " + str(self.tem_var.get())
        self.game_rules_text += "\nTake insurance: " + str(self.ti_var.get())

        
        try:
            self.game_rules_Text.delete('1.0', tk.END)
        except:
            pass
        
        self.game_rules_Text.insert('1.0', self.game_rules_text)
        #self.game_rules_Text['state']='disabled'
        self.game_rules_Text.update()
        
        # Stats
        self.game_stats_text = "GAME EXPECTED VALUE:"
        if self.got_book == "finished":
            ev, cost = self.get_total_ev()
            self.ev = ev
            self.game_stats_text += "\nTotal EV: " + format(ev, "^-14.9f")
            self.game_stats_text += "\nDeviation Cost: " + \
                format(cost, "^-12.7f")
            
        else:
            self.game_stats_text += "\nPending..."
        try:
            self.game_stats_Text.delete('1.0', tk.END)
        except:
            pass
        self.game_stats_Text.insert('1.0', self.game_stats_text)
        self.game_stats_Text.update()
        
              
    def toggle(self, button):
        """Handles overhead for some menu selections."""
        if button == 'any hand' or button == 'first two' or \
           button == '9 10 11' or button == '10 11':
            self.double_var.set(button)
        if button in ['any hand','first two','9 10 11','10 11','DHS17']:
            self.reset_plays()
        if button in ['msh2','msh3','msh4','DAS','HSA','RSA']:
            self.reset_plays(type='pair')
        self.show_game_info()

    def set_deck_infinite(self):
        """Sets the deck choice to infinite."""
        if self.deck_choice != 'infinite':
            self.got_book = "waiting"
            self.reset_plays()
                        
        try:
            self.ev_canvas.delete("all")
        except Exception:
            pass

        try:
            self.deck_finite_window.destroy()         
        except Exception:
            pass

        try:    
            self.deck_custom_window.destroy()
        except Exception:
            pass

        self.deck = ONE_DECK.copy()
        self.deck_choice = 'infinite'
        self.show_game_info()
       

    def set_deck_finite(self):
        """Sets the deck choice to finite."""
        if self.deck_choice != 'finite':
            self.got_book = "waiting"
            self.reset_plays()

        try:
            self.deck_custom_window.destroy()
        except Exception:
            pass

        try:
            self.deck_finite_window.destroy()
        except Exception:
            pass

        self.deck_finite_window = tk.Toplevel(self)
        self.deck_finite_window.title("Finite Deck")
        self.deck_finite_window.geometry("120x210")

        self.deck_choice = 'finite'
            
        self.finite_deck_frame = tk.Frame(
                self.deck_finite_window, 
                bd=2, 
                relief='raised',
                width=100, 
                height=190
                )
        self.finite_deck_frame.place(x=10, y=10)
        self.finite_deck_add_deck_button = tk.Button(
                self.finite_deck_frame,
                text = "Add Deck",
                command=self.add_deck
                )
        self.finite_deck_add_deck_button.place(x=10, y=10, width=80, height=30)
        self.finite_deck_label = tk.Label(
                self.finite_deck_frame, 
                text = "Deck Count"
                )
        self.finite_deck_label.place(x=10, y=45)
        self.finite_deck_canvas = tk.Canvas(
                self.finite_deck_frame, 
                background = 'white',
                width=60, 
                height=40
                )
        self.finite_deck_canvas.place(x=20,y=70)
        self.finite_deck_update()
        self.finite_deck_remove_deck_button = tk.Button(
                self.finite_deck_frame,
                text = "Remove Deck",
                wraplength=80,
                command=self.remove_deck
                )
        self.finite_deck_remove_deck_button.place(
                x=10, 
                y=120, 
                width=80, 
                height=50
                )
        self.show_game_info()

    def set_deck_custom(self):
        """Sets the deck choice to custom."""

        try:
            self.deck_finite_window.destroy() 
        except Exception:
            pass

        self.got_book = "waiting"
        self.update_book_build_status()
        
        try:
            self.ev_canvas.delete("all")
        except Exception:
            pass

        if self.deck_choice != 'custom':
            self.deck_choice = 'custom'
            self.reset_plays()


        self.deck_custom_window = tk.Toplevel(self)
        self.deck_custom_window.title("Custom Deck")
        self.deck_custom_window.geometry("560x250")
        
        self.custom_deck_frame = tk.Frame(
                self.deck_custom_window, 
                bd=2, 
                relief='raised',
                width=540, 
                height=230
                )
        self.custom_deck_frame.place(x=10, y=10)
        self.custom_deck_card_values_label = tk.Label(
                self.custom_deck_frame, 
                text = "Card values"
                )
        self.custom_deck_card_values_label.place(x=230, y=10)
        self.custom_deck_card_counts_label = tk.Label(
                self.custom_deck_frame, 
                text = "Card counts"
                )
        self.custom_deck_card_counts_label.place(x=230, y=190)

        self.custom_deck_value_labels = []
        self.custom_deck_plus_buttons = []
        self.custom_deck_minus_buttons = []
        self.custom_deck_canvases = []
        self.custom_deck_canvas_texts = []

        for index, card in enumerate(CARD_VALUES):
            value_label = tk.Label(
                    self.custom_deck_frame, 
                    text = NUM_TO_TEXT[card]
                    )
            value_label.place(x=30 + index*50, y=30)
            self.custom_deck_value_labels.append(value_label)
            plus_button = tk.Button(
                    self.custom_deck_frame,
                    text = "+",
                    command=lambda card=card: 
                    self.custom_deck_add_card(card)
                    )
            plus_button.place(x=10 + index*50, y=50, width=35, height=35)
            self.custom_deck_plus_buttons.append(plus_button)
            minus_button = tk.Button(
                    self.custom_deck_frame,
                    text = "-",
                    command=lambda card=card: 
                    self.custom_deck_subtract_card(card)
                    )
            minus_button.place(x=10 + index*50, y=90, width=35, height=35)
            self.custom_deck_minus_buttons.append(minus_button)
            count_canvas = tk.Canvas(
                    self.custom_deck_frame, 
                    background = 'white',
                    width=35, 
                    height=35
                    )
            count_canvas.place(x=10 + index*50,y=135)
            self.custom_deck_canvases.append(count_canvas)
            canvas_text = count_canvas.create_text(
                    20, 
                    20,
                    text=str(self.deck.count(card)),
                    font=('Helvetica', 18, 'bold'),
                    justify='center'
                    )
            self.custom_deck_canvas_texts.append(canvas_text)
        reset_button = tk.Button(
                self.custom_deck_frame,
                text = "Reset to one deck",
                command=self.custom_deck_reset
                )
        reset_button.place(x=360, y=185, width=135, height=35)
        self.show_game_info()
                            
    def custom_deck_reset(self):
        """Resets the current deck to be one regular deck."""
        self.deck = ONE_DECK.copy()
        self.custom_deck_update_canvas()
        self.show_game_info()

    def custom_deck_add_card(self, card):
        """Adds a card to the current deck."""
        self.deck.append(card)
        self.custom_deck_update_canvas()
        self.show_game_info()
                
    def custom_deck_subtract_card(self, card):
        """Subtracts a card from the current deck."""
        if self.deck.count(card) >= 4:
            self.deck.remove(card)
            self.custom_deck_update_canvas()
        else:
            messagebox.showinfo(
                    'Custom deck message', 
                    "Minimum of three of each card required."
                    )
        self.show_game_info()

    def custom_deck_update_canvas(self):
        """Updates the displayed number of each card in the custom deck 
        window."""
        for index, card in enumerate(CARD_VALUES):
            self.custom_deck_canvases[index].delete("all")
            canvas_text = self.custom_deck_canvases[index].create_text(
                    20, 
                    20,
                    text=str(self.deck.count(card)),
                    font=('Helvetica', 18, 'bold'),
                    justify='center'
                    )
            self.custom_deck_canvas_texts[index] = canvas_text
            self.custom_deck_canvases[index].update()       
        
    def add_deck(self):
        """Adds a deck for the finite deck choice."""
        self.num_decks += 1
        self.finite_deck_update()

    def remove_deck(self):
        """Removes a deck for the finite deck choice."""
        if self.num_decks > 1:
            self.num_decks -= 1
            self.finite_deck_update()

    def finite_deck_update(self):
        """Updates self.deck to accommodate add and remove deck choices."""
        self.show_game_info()
        self.finite_deck_canvas.delete("all")
        self.finite_deck_canvas.create_text(
                30, 
                20,
                text=str(self.num_decks),
                font=('Helvetica', 18, 'bold'),
                justify='center'
                )
        self.finite_deck_canvas.update()
        self.deck = self.num_decks * ONE_DECK

    def initialize_show_frame(self):
        """Initializes the plays shown in the main window."""
        play = '?'
        # Hard Hands

        start_row = 0
        start_col = 280
        
        label = tk.Label(
                self.show_frame, 
                text='Hard Hands', 
                background='gold', 
                font = (None,15)
                )
        label.place(x=start_col + 110, y=start_row)

        col = 30
        for up_card in range(2, 12):
            duc = NUM_TO_TEXT[up_card]
            label = tk.Label(self.show_frame, text = duc, font = (None, 15))
            label.place(x=start_col + col, y=start_row + 30)
            col += 30

        row = 60
        for hard_hand in range(8, 18):
            label = tk.Label(self.show_frame, text = str(hard_hand),
                  font = (None, 15))
            label.place(x=start_col, y = start_row + row)

            col = 30
            for up_card in range(2, 12):
                if up_card == 11:
                    duc = 1
                else:
                    duc = up_card
                label_index = self.get_playlist_index_from_book_tuple(
                        hard_hand, 
                        'hard', 
                        duc
                        )
                self.playlist_stringvars[label_index].set(play)
                self.playlist_labels[label_index].place(
                        x = start_col + col,
                        y = start_row + row
                        )
                self.playlist_labels[label_index].config(bg = COLORS[play])

                col += 30
            row += 30

        # Soft Hands

        start_row = 0
        start_col = 620
          
        label = tk.Label(
                self.show_frame, 
                text = 'Soft Hands', 
                font = (None, 15),
                background = 'gold'
                )
        label.place(x=start_col + 110, y=start_row)

        row = 30
        col = 30

        for up_card in range(2, 12):
            duc=NUM_TO_TEXT[up_card]
            label = tk.Label(self.show_frame, text = duc, font = (None, 15))
            label.place(x=start_col + col, y=start_row + row)
            col += 30

        row += 30

        for soft_hand in range(13, 21):
            label = tk.Label(self.show_frame, text = str(soft_hand),
                  font = (None, 15))
            label.place(x=start_col, y = start_row + row)

            col = 30
        
            for up_card in range(2, 12):
                if up_card == 11:
                    duc = 1
                else:
                    duc = up_card
                label_index = self.get_playlist_index_from_book_tuple(
                        soft_hand, 'soft', duc)
                self.playlist_stringvars[label_index].set(play)
                self.playlist_labels[label_index].place(
                        x = start_col + col,
                        y = start_row + row
                        )
                self.playlist_labels[label_index].config(bg = COLORS[play])

                col += 30
            row += 30

        # Pairs
        start_col = 960
        start_row = 0

        label = tk.Label(self.show_frame, text = 'Pairs', font = (None, 15),
                  background = 'gold')
        label.place(x=start_col + 140, y=start_row)
        
        row = 30
        col = 50

        for up_card in range(2, 12):
            duc=NUM_TO_TEXT[up_card]
            label = tk.Label(self.show_frame, text = duc, font = (None, 15))
            label.place(x=start_col + col, y=start_row + row)
            col += 30

        row += 30
        col = 0

        for pair in range(2, 12):
            col = 0
            pair_txt = NUM_TO_TEXT[pair]
            label = tk.Label(self.show_frame,
                             text = pair_txt + ', ' + pair_txt,
                             font = (None, 15))
            label.place(x=start_col, y = start_row + row)
            col += 50

            if pair == 11:
                pair_of = 1
            else:
                pair_of = pair
            
            for up_card in range(2, 12):
                if up_card == 11:
                    duc = 1
                else:
                    duc = up_card
                label_index = self.get_playlist_index_from_book_tuple(
                        pair_of, 'pair', duc)
                self.playlist_stringvars[label_index].set(play)
                self.playlist_labels[label_index].place(
                       x = start_col + col,
                       y = start_row + row
                       )
                self.playlist_labels[label_index].config(bg = COLORS[play])

                col += 30

            row += 30

        # Legend
        legend_frame = tk.Frame(
                self.show_frame, 
                bd=2, 
                relief='raised',
                width=320, 
                height=65
                )
        legend_frame.place(x=620, y=310)
        legend_stand = tk.Label(
                legend_frame, 
                text='S',
                font=(None, 15), 
                background=COLORS['S']
                )
        legend_stand.place(x=0, y=0)
        legend_stand_a = tk.Label(
                legend_frame, 
                text=': Stand',
                font=(None, 15)
                )
        legend_stand_a.place(x=20, y=0)
        legend_hit = tk.Label(
                legend_frame, 
                text='H',
                font=(None, 15), 
                background=COLORS['H']
                )
        legend_hit.place(x=115, y=0)
        legend_hit_a = tk.Label(
                legend_frame, 
                text=': Hit',
                font=(None, 15)
                )
        legend_hit_a.place(x=135, y=0)
        legend_double = tk.Label(
                legend_frame, 
                text='D',
                font=(None, 15), 
                background=COLORS['D']
                )
        legend_double.place(x=200, y=0)
        legend_double_a = tk.Label(
                legend_frame, 
                text=': Double',
                font=(None, 15)
                )
        legend_double_a.place(x=220, y=0)
        legend_double = tk.Label(
                legend_frame, 
                text='P',
                font=(None, 15), 
                background=COLORS['P']
                )
        legend_double.place(x=0, y=30)
        legend_double_a = tk.Label(
                legend_frame, 
                text=': Split',
                font=(None, 15)
                )
        legend_double_a.place(x=20, y=30)
        legend_deviation = tk.Label(
                legend_frame, 
                text='  ',
                font=(None, 15), 
                background=DEVIATION_COLOR
                )
        legend_deviation.place(x=115, y=30)
        legend_deviation_a = tk.Label(
                legend_frame, 
                text=': Play Deviation',
                font=(None, 15)
                )
        legend_deviation_a.place(x=135, y=30)
        self.show_frame.update()
        
    # Helper Functions
    def get_valid_hand_and_hand_prob(self, fpc, spc, duc):
        """Returns a boolean indicating whether the specified hand is legit 
        based on the self.deck, along with the probability for that hand."""
        valid_hand = True
        if self.deck_choice == 'infinite':
            hand_prob = ONE_DECK_DIST[fpc] * \
                        ONE_DECK_DIST[spc] * \
                        ONE_DECK_DIST[duc]
        else:
            temp_deck = self.deck.copy()
            hand_prob = 1
            cards = [fpc, spc, duc]
            for card in cards:
                if temp_deck.count(card) > 0:
                    hand_prob *= (temp_deck.count(card) / len(temp_deck))
                    temp_deck.remove(card)
                else:
                    valid_hand = False
        return valid_hand, hand_prob
            
    def hard_hand_book_lookup(self, pht, duc):
        """Returns the best play based on the average EVs for a hard player 
        hand total, along with a list of those average EVs.""" 
            
        total_ev = [0, 0, 0] # S, H, D
        total_prob = 0
        
        for cards in HARD_HAND_COMP[pht]:
            valid_hand, hand_prob = self.get_valid_hand_and_hand_prob(
                    cards[0],
                    cards[1],
                    duc)
            if valid_hand:
                if cards[0] != cards[1]:
                    hand_prob *= 2

                total_prob += hand_prob
                total_ev[0] += hand_prob * \
                        book[(cards[0], cards[1], duc)][1] # stand EV
                total_ev[1] += hand_prob * \
                        book[(cards[0], cards[1], duc)][2] # hit EV
                total_ev[2] += hand_prob * \
                        book[(cards[0], cards[1], duc)][3] # double EV

        if total_prob == 0:
            return 'X' , [0, 0, 0]
        
        total_ev = [ev / total_prob for ev in total_ev]
        max_ev = max(total_ev)
        index_max_ev = total_ev.index(max_ev)
        best_play = REV_EV_INDEX[index_max_ev]
        return best_play, total_ev

    def book_lookup(self, player_card_list, duc, hard_hand_deviations_ok=True):
        """If player card list contains just two cards, the best play and EV 
        list for those cards and duc combination are returned. If the best 
        hand of the player card list is soft, the equivalent two card soft 
        hand best play and EV list is returned from the book. Otherwise, 
        player card list amounts to a hard hand and the average hard hand play 
        and EV list is returned."""

        if len(player_card_list) == 2 and \
               player_card_list[0] == player_card_list[1]:
            hard_hand_deviations_ok = True

        if len(player_card_list) == 2 and hard_hand_deviations_ok:
            card1, card2 = player_card_list[0], player_card_list[1]
            # Book doesn't contain duplicate entries.
            # Card1 and card2 must be in numerical order.
            if card1 > card2:
                card1, card2 = card2, card1
            return book[(card1, card2, duc)][0], book[(card1, card2, duc)][1:] 

        pht, hard_or_soft = self.best_hand_from_card_list(player_card_list)
        assert pht >= 4
        if pht > 21:
            return 'S', [-1, -1, -1]
        if hard_or_soft == 'soft':
            return book[(1, pht - 11, duc)][0], book[(1, pht - 11, duc)][1:]
        return self.hard_hand_book_lookup(pht, duc)                            

    def no_split_book_lookup(self, player_card_list, duc):
        """This function, in conjunction with convert_best_total_to_two_cards,
        is used to get the equivalent book play for a 3+ card hand, excluding
        a best play of split."""
        play, ev_list = self.book_lookup(player_card_list, duc)
        if play != 'P':
            return play, ev_list
        else:
            best_index = ev_list.index(max(ev_list[0:3]))
            return REV_EV_INDEX[best_index], ev_list
            
    def best_total(self, hs, ac):
        """Returns the best total from the provided hard sum and ace count,
        and whether the total is hard or soft."""
        if ac >= 1 and hs + ac < 12:
            best = hs + ac + 10
            hard_or_soft = 'soft'
        else:
            best = hs + ac
            hard_or_soft = 'hard'
        return best, hard_or_soft

    def best_hand_from_card_list(self, card_list):
        """Returns the best total from a card list, along with whether or not
        the total is hard or soft."""
        hard_sum = 0
        ace_count = 0
        for card in card_list:
            if card == 1:
                ace_count += 1
            else:
                hard_sum += card
        return self.best_total(hard_sum, ace_count)
        
    def get_card_dist(self, deck):
        """Returns a dictionary whose keys represent the cards in the passed
        deck and whose values indicate the corresponding percentage that those
        cards are of the deck."""

        deck_size = len(deck)
        dist = {1:0, 2:0, 3:0, 4:0, 5:0,
                6:0, 7:0, 8:0, 9:0, 10:0}
        for card in dist.keys():
            dist[card] = deck.count(card) / deck_size
        return dist


    def blackjack_chance(self, deck=None):
        """Returns the chance of getting a blackjack from the passed deck."""
        if self.deck_choice == 'infinite':
            return 2 * ONE_DECK_DIST[1] * ONE_DECK_DIST[10]
        else:
            deck_dist = self.get_card_dist(deck)
            return 2 * deck_dist[1] * deck_dist[10]
        
    def get_playlist_index_from_book_tuple(self, total, hand_type, duc):
        """Returns the index of the play labels shown on the main screen
        for a passed total, hand_type and duc combination."""

        assert hand_type in ['hard', 'soft', 'pair']
        type_offset = {'hard':0, 'soft':100, 'pair':180}
        duc_offset = {2:0, 3:1, 4:2, 5:3, 6:4, 7:5, 8:6, 9:7, 10:8, 1:9}
        if hand_type == 'hard':
            assert total >= 8 and total <= 17
            row_offset = (total - 8) * 10
            return type_offset[hand_type] + row_offset + duc_offset[duc]
        elif hand_type == 'soft':
            assert total >= 13 and total <= 20
            row_offset = (total - 13) * 10
            return type_offset[hand_type] + row_offset + duc_offset[duc]
        else:
            assert total >= 1 and total <= 10
            if total != 1:
                row_offset = (total - 2) * 10
            else:
                row_offset = 90
            return type_offset[hand_type] + row_offset + duc_offset[duc]

    def get_book_tuple_from_playlist_index(self, index):
        """Returns a book tuple of total, hand_type, and duc for a passed
        play label index."""
        
        assert index >=0 and index < 280
        duc_offset = {0:2, 1:3, 2:4, 3:5, 4:6, 5:7, 6:8, 7:9, 8:10, 9:1}
        if index < 100:
            hand_type = 'hard'
            total = floor(index / 10) + 8
            duc = duc_offset[index % 10]
        elif index >= 100 and index < 180:
            hand_type = 'soft'
            total = floor((index - 100) / 10) + 13
            duc = duc_offset[index % 10]
        else:
            hand_type = 'pair'
            total = floor((index - 180) / 10) + 2
            if total == 11:
                total = 1
            duc = duc_offset[index % 10]
        return (total, hand_type, duc)

    def double_check(self, play, player_card_list, duc, split=False):
        """Checks whether the rules allow a double. If the passed play is not 
        a double, it is just returned. If it is a double, a double is returned 
        if the rules allow double, otherwise the best play between 'S' and 'H' 
        is returned. The passed split argument indicates whether the current 
        player_card_list is part of a split hand. This is important to know in 
        case double after split is disallowed."""
        
        if play == 'D':
            pht, hard_or_soft = self.best_hand_from_card_list(player_card_list)             
            if ((len(player_card_list) >= 2 and \
                 self.double_var.get() == "any hand") or \
               len(player_card_list) == 2 and \
                (self.double_var.get() == "first two" or \
               (self.double_var.get() == "9 10 11" and \
                hard_or_soft == 'hard' and pht in [9, 10, 11]) or \
               (self.double_var.get() == "10 11" and \
                hard_or_soft == 'hard' and pht in [10, 11]))) and \
               (split == False or (split == True and self.das_var.get())):
                best_play = 'D'
            else:
                # Double not ok, so return the best play between 'S' and 'H'
                _, ev_list = self.book_lookup(player_card_list, duc)
                if ev_list[0] > ev_list[1]:
                    best_play = 'S'
                else:
                    best_play = 'H'
            return best_play
        else:
            return play
                
    # High Level Functions

    def show_play_deviations(self):
        """Outputs hard hand play deviations to standard out."""
        are_there_deviations = False
        for pht in range(20, 5, -1):
            for duc in range(10, 0, -1):
                if len(HARD_HAND_COMP[pht]) > 1:
                    book_play, _ = self.hard_hand_book_lookup(pht, duc)
                    for cards in HARD_HAND_COMP[pht]:
                        deviation_play, _ = self.no_split_book_lookup(
                                [cards[0],
                                cards[1]],
                                duc
                                )
                        if book_play != deviation_play:
                            print(f'Book Play for {cards}, duc: {duc} is '
                                  f'{book_play}. '
                                  f'Deviation play is: {deviation_play}.')
                            are_there_deviations = True
        if not are_there_deviations:
            print('No hard hand play deviations detected.')
        else:
            print('Finished hard hand comp play deviations check.')

    def sim_play(self, fpc, spc, duc, play, allow_bj, deck=None):
        """plays the given hand and returns its ev."""
        
        if self.deck_choice == 'infinite':
            play_deck = ONE_DECK

        else:
            play_deck = deck.copy()
            play_deck.remove(fpc)
            play_deck.remove(spc)
            play_deck.remove(duc)

        pht, hard_or_soft = self.best_hand_from_card_list([fpc, spc])

        if pht == 21:
            player_bj = True
        else:
            player_bj = False


        total_ev = 0

        if allow_bj == False:
            # We don't want to allow a dealer blackjack here because we are
            # simulating play assuming the dealer didn't already get one.        
            if duc == 1:
                dealer_down_card_deck = \
                    [card for card in play_deck if card != 10]
            elif duc == 10:
                dealer_down_card_deck = \
                    [card for card in play_deck if card != 1]
            else:
                dealer_down_card_deck = play_deck.copy()          
        else:
            dealer_down_card_deck = play_deck.copy()            

        ddc = random.choice(dealer_down_card_deck)

        if self.deck_choice != 'infinite':
            play_deck.remove(ddc)

        dealer_cards = [duc, ddc]
        dht, hard_or_soft = self.best_hand_from_card_list(dealer_cards)


        # Deal with BJs
        if dht == 21:
            dealer_bj = True
        else:
            dealer_bj = False

        assert not (dealer_bj and not allow_bj)

        if allow_bj == True:
            if player_bj:
                if duc == 1:
                    if self.tem_var.get():
                        return 1
                    else:
                        if dealer_bj:
                            return 0
                        else:
                            return BLACKJACK_PAY[self.fullpay_var.get()]
                elif dealer_bj:
                    return 0
                else:
                    return BLACKJACK_PAY[self.fullpay_var.get()]
            else:
                if duc == 1:
                    if self.ti_var.get():
                        if dealer_bj:
                            return 0
                        else:
                            total_ev -= 0.5
                if dealer_bj:
                    return -1
                
        # No dealer or player BJ past here
        if play == 'S':
            hands_result = [pht]
            bet_multiplier = [1]

        # No need to check if double is allowed here, since play was 
        # explicitly called with it.
        elif play == 'D':
            player_hands =[[fpc, spc]]
            double_card = random.choice(play_deck)
            if self.deck_choice != 'infinite':
                play_deck.remove(double_card)

            player_hands[0].append(double_card)
            pht, hard_or_soft = self.best_hand_from_card_list(player_hands[0])
            bet_multiplier = [2]
            if pht >= 22:
                return -2

            hands_result = [pht]
                     
        elif play == 'H':
            player_hands =[[fpc, spc]]
            book_play = 'H'
            bet_multiplier = [1]
            while book_play != 'S':
                hit_card = random.choice(play_deck)
                if self.deck_choice != 'infinite':
                    play_deck.remove(hit_card)

                player_hands[0].append(hit_card)
                pht, hard_or_soft = self.best_hand_from_card_list(
                        player_hands[0]
                        )
                
                if pht >= 22:
                    return -1
                book_play, _ = self.no_split_book_lookup(player_hands[0], duc)
                book_play = self.double_check(book_play, player_hands[0], duc)
                if book_play == 'D':
                    double_card = random.choice(play_deck)
                    if self.deck_choice != 'infinite':
                        play_deck.remove(double_card)
                    player_hands[0].append(double_card)
                    pht, hard_or_soft = self.best_hand_from_card_list(
                            player_hands[0]
                            )
                    bet_multiplier[0] += 1
                    book_play = 'S'
            hands_result = [pht]
            
            
        elif play == 'P':
        
            assert fpc == spc
            max_split_hands = self.msh_var.get()
            if fpc == 1 and not self.rsa_var.get():
                max_split_hands = 2

            player_hands = [[fpc],[spc]]
            hands_result = []
            bet_multiplier = []
            current_hand = 0
            player_turn_done = False
            event = ''
            
            while not player_turn_done:
                draw_card = random.choice(play_deck)
          
                if self.deck_choice != 'infinite':
                    play_deck.remove(draw_card)
                # Add additional split cards to a new hand if we get an
                # additional split card and are not already at max split hands.
                while draw_card == fpc and len(player_hands) < max_split_hands:
                    event += 'p'
                    player_hands.append([draw_card])
                    draw_card = random.choice(play_deck)

                    if self.deck_choice != 'infinite':
                        play_deck.remove(draw_card)
                # This draw_card is ALWAYS the second card to the current
                # split hand.           
                    
                if len(event) < 4 and event.count('p') < 2 and \
                   (max_split_hands != 3 or event.count('p') == 0):
                    event += 'm'

                player_hands[current_hand].append(draw_card)
                pht, hard_or_soft = self.best_hand_from_card_list(
                        player_hands[current_hand])
                # We assume a normal non-double hand. 
                # If we get to double later on, we add 1 to this.
                bet_multiplier.append(1)
                            
                if fpc == 1 and not self.hsa_var.get():
                    pass     
                else:       
                    book_play, _ = self.no_split_book_lookup(
                            player_hands[current_hand], duc)
                    assert book_play in ['S', 'H', 'D']
                    # Deal with double opportunity
                    book_play = self.double_check(
                            book_play,
                            player_hands[current_hand],
                            duc,
                            True)
                    if book_play == 'D':
                        bet_multiplier[current_hand] += 1
                        double_card = random.choice(play_deck)
                        
                        if self.deck_choice != 'infinite':
                            play_deck.remove(double_card)
                        player_hands[current_hand].append(double_card)
                        pht, _ = self.best_hand_from_card_list(
                                player_hands[current_hand]
                                )
                    else:
                        # Either hit or stand
                        while book_play != 'S':                      
                            draw_card = random.choice(play_deck)
                            
                            if self.deck_choice != 'infinite':
                                play_deck.remove(draw_card)
                            player_hands[current_hand].append(draw_card)
                            pht, hard_or_soft = self.best_hand_from_card_list(
                                    player_hands[current_hand]
                                    )
                            if pht > 21:
                                book_play = 'S'
                            else:
                                book_play, _ = self.no_split_book_lookup(
                                        player_hands[current_hand], duc)
                                book_play = self.double_check(
                                        book_play,
                                        player_hands[current_hand],
                                        duc,
                                        True
                                        )
                                if book_play == 'D':
                                    bet_multiplier[current_hand] += 1
                                    double_card = random.choice(play_deck)
                                    
                                    if self.deck_choice != 'infinite':
                                        play_deck.remove(double_card)
                                    player_hands[current_hand].append(
                                            double_card
                                            )
                                    pht, _ = self.best_hand_from_card_list(
                                            player_hands[current_hand])
                                    book_play = 'S'
                            
                
                hands_result.append(pht)
                current_hand += 1   
                if current_hand >= len(player_hands):
                    player_turn_done = True

        #Pair stats
        global two_hand_count
        global three_hand_count
        global four_hand_count
        global two_hand_ev_summation_list
        global three_hand_ev_summation_list
        global four_hand_ev_summation_list
        global mm_ev_summation_list
        global p_ev_summation_list
        global mp_ev_summation_list
        global pp_ev_summation_list
        global pmp_ev_summation_list
        global mpp_ev_summation_list
        global pmmp_ev_summation_list
        global mpmp_ev_summation_list
        global pmmm_ev_summation_list
        global mpmm_ev_summation_list
        global event_hand_counts
        global ddc_is_pc_count
      
        if DEBUG >= 2:
            if play == 'P':
                if max_split_hands == 2:
                    assert event in ['mm']
                elif max_split_hands == 3:
                    assert event in ['mm', 'p', 'mp']
                elif max_split_hands == 4:
                    assert event in  ['mm', 'pmmm', 'mpmm', 'pp', 
                                     'pmp', 'mpp', 'mpmp', 'pmmp']

                if len(hands_result) == 2:
                    two_hand_count += 1
                        
                if len(hands_result) == 3:
                    three_hand_count += 1
                
                if len(hands_result) == 4:
                    four_hand_count += 1
               
                if ddc == fpc:
                    ddc_is_pc_count[event] += 1
        
        # Now dealer turn
        dht, hard_or_soft = self.best_hand_from_card_list(dealer_cards)
        while (dht == 17 and hard_or_soft == 'soft' and \
               self.dhs17_var.get()) or (dht < 17):
            dealer_draw_card = random.choice(play_deck)
            if self.deck_choice != 'infinite':
                play_deck.remove(dealer_draw_card)
            
            dealer_cards.append(dealer_draw_card)
            dht, hard_or_soft = self.best_hand_from_card_list(dealer_cards)

        total_ev_list = []
        for index, pht in enumerate(hands_result):
            assert bet_multiplier[index] == 1 or bet_multiplier[index] == 2
            # Player busts first
            if pht > 21:
                total_ev_list.append(bet_multiplier[index] * (-1))
            elif dht > 21:
                total_ev_list.append(bet_multiplier[index])
            elif pht > dht:
                total_ev_list.append(bet_multiplier[index])
            elif dht > pht:
                total_ev_list.append(bet_multiplier[index] * (-1))
            else:
                total_ev_list.append(0)    
  
        # Process pair stats if Debug >= 2

        
        if play == 'P' and DEBUG >= 2:

            event_hand_counts[event] += 1
            hands = len(player_hands)
            assert hands in [2, 3, 4]
            
            if hands == 2:
                for i in range(0, 2):
                    two_hand_ev_summation_list[i] +=  total_ev_list[i]
                    mm_ev_summation_list = two_hand_ev_summation_list   
                       
            elif hands == 3:
                for i in range(0, 3):
                    three_hand_ev_summation_list[i] += total_ev_list[i]
                    if max_split_hands == 3:
                        if event == 'p':
                            p_ev_summation_list[i] += total_ev_list[i]
                        elif event == 'mp':
                            mp_ev_summation_list[i] += total_ev_list[i]
                        else:
                            print(f'(sim_play) unexpected event {event} '
                                  f'expected either p or mp '
                                  f'\nmsh: {max_split_hands}')
                    if max_split_hands == 4:
                        if event == 'pmmm':
                            pmmm_ev_summation_list[i] += total_ev_list[i]
                        elif event == 'mpmm':
                            mpmm_ev_summation_list[i] += total_ev_list[i]
                        else:
                            print(f'(sim_play) unexpected event {event} '
                                  f'expected either pmmm or mpmm '
                                  f'\nmsh: {max_split_hands}')

            elif hands == 4:
                for i in range(0, 4):
                    four_hand_ev_summation_list[i] += total_ev_list[i]
                    if event == 'pp':
                        pp_ev_summation_list[i] += total_ev_list[i]
                    if event == 'mpp':
                        mpp_ev_summation_list[i] += total_ev_list[i]
                    if event == 'pmp':
                        pmp_ev_summation_list[i] += total_ev_list[i]
                    if event == 'pmmp':
                        pmmp_ev_summation_list[i] += total_ev_list[i]
                    if event == 'mpmp':
                        mpmp_ev_summation_list[i] += total_ev_list[i]

        return sum(total_ev_list)

    def get_total_ev(self):
        """Returns the total EV for the selected rules and deck, including
        the effect of any play deviations. The cost of play deviations is
        also returned."""
        total_ev = 0
        total_deviation_cost = 0
        player_hand_chance_cumm_sum = 0
        total_player_bj_chance = 0
        total_dealer_bj_chance = 0
        total_both_bj_chance = 0

        for fpc in range(1, 11):
            for spc in range(1, 11):
                for duc in range(1, 11):
                    valid_hand, player_hand_chance = \
                            self.get_valid_hand_and_hand_prob(
                                    fpc, 
                                    spc, 
                                    duc
                                    )
                    if not valid_hand:
                        continue

                    pht, hard_or_soft = self.best_hand_from_card_list(
                            [fpc, spc]
                            )
                    if pht == 21:
                        total_player_bj_chance += player_hand_chance
                        if duc == 1:
                            if self.tem_var.get():
                                hand_ev = 1                            
                            else:
                                # if dealer down card is 10, we just push, 
                                # so the ev here should be the chance that 
                                # the dealer has some card other than ten, 
                                # times the blackjack pay.
                                if self.deck_choice == 'infinite':
                                    chance_ddc_not_ten = 1 - ONE_DECK_DIST[10]
                                else:
                                    chance_ddc_not_ten = 1 - \
                                        (self.deck.count(10) / \
                                        len(self.deck))
                                hand_ev =  chance_ddc_not_ten * \
                                          BLACKJACK_PAY[self.fullpay_var.get()]
                                total_both_bj_chance += player_hand_chance * \
                                        (1 - chance_ddc_not_ten)
                                total_dealer_bj_chance += \
                                        player_hand_chance * \
                                        (1 - chance_ddc_not_ten)
                        elif duc == 10:
                            # we win if ddc is not ace, otherwise we push
                            if self.deck_choice == 'infinite':
                                chance_ddc_not_ace = 1 - ONE_DECK_DIST[1]
                            else:
                                chance_ddc_not_ace = 1 - \
                                        (self.deck.count(1) / \
                                        len(self.deck))
                            hand_ev = chance_ddc_not_ace * \
                                      BLACKJACK_PAY[self.fullpay_var.get()]
                            total_both_bj_chance += player_hand_chance * \
                                                    (1 - chance_ddc_not_ace)
                            total_dealer_bj_chance += player_hand_chance * \
                                                      (1 - chance_ddc_not_ace)
                        else:
                            hand_ev = BLACKJACK_PAY[self.fullpay_var.get()]
                    else:
                        # now we just have to worry about dealer blackjacks
                        # For now, use the play displayed on the main frame,
                        # and not the individual hard hand play which may be
                        # different.


                        book_play, _ = self.book_lookup([fpc, spc], duc, False)
                        _, ev_list = self.book_lookup([fpc, spc], duc, True)

                        # Ensure we use any user-set play deviations. These
                        # only apply to hands displayed in the main frame.
                        
                        if (pht >= 8 and pht <= 17 and \
                                hard_or_soft == 'hard') or \
                           (pht >= 13 and pht <= 20 and \
                                hard_or_soft == 'soft') or \
                           fpc == spc:
                            if fpc == spc:
                                hand_type = 'pair'
                                total = fpc
                            else:
                                hand_type = hard_or_soft
                                total = pht
                            label_index = \
                                self.get_playlist_index_from_book_tuple(
                                    total,
                                    hand_type,
                                    duc
                                    )
                            display_play = \
                                self.playlist_stringvars[label_index].get()
                        else:
                            display_play = book_play

                        if display_play not in ['S', 'H', 'D', 'P']:
                            print(f'Error in get_total_ev. '
                                  f'\nfpc: {fpc} spc: {spc} duc: {duc} '
                                  f'label_index: {label_index}'
                                  f'display_play: {display_play}')
                            raise Exception
                        if book_play == display_play:
                            interim_ev = ev_list[EV_INDEX[book_play]]
                        else:
                            interim_ev = ev_list[EV_INDEX[display_play]]
                            total_deviation_cost += \
                                    player_hand_chance * \
                                    (interim_ev - \
                                    ev_list[EV_INDEX[book_play]])
                        if duc == 1:
                            hand_ev = 0
                            if self.deck_choice == 'infinite':
                                chance_ddc_is_ten = ONE_DECK_DIST[10]
                            else:
                                chance_ddc_is_ten = (self.deck.count(10) / \
                                                     len(self.deck))
                            # offer insurance 
                            # (ins. bet is 0.5 main bet, and pays 2:1)
                            if self.ti_var.get():      
                                hand_ev += chance_ddc_is_ten  
                                hand_ev -= (1 - chance_ddc_is_ten) * 0.5   
                            hand_ev -= chance_ddc_is_ten
                            hand_ev += (1 - chance_ddc_is_ten) * interim_ev
                            total_dealer_bj_chance += player_hand_chance * \
                                    chance_ddc_is_ten
                        elif duc == 10:
                            hand_ev = 0
                            if self.deck_choice == 'infinite':
                                chance_ddc_is_ace = ONE_DECK_DIST[1]
                            else:
                                chance_ddc_is_ace = (self.deck.count(1) / \
                                                     len(self.deck))    
                            hand_ev += (-1) * chance_ddc_is_ace
                            hand_ev += (1 - chance_ddc_is_ace) * interim_ev
                            total_dealer_bj_chance += player_hand_chance * \
                                    chance_ddc_is_ace
                        else:
                            hand_ev = interim_ev
                        
                    total_ev += player_hand_chance * hand_ev
                    player_hand_chance_cumm_sum += player_hand_chance
       
        return total_ev, total_deviation_cost
                    

    def print_ev(self, deck=None):
        eleven_to_one = {1:1,
                         2:2,
                         3:3,
                         4:4,
                         5:5,
                         6:6,
                         7:7,
                         8:8,
                         9:9,
                         10:10,
                         11:1
                         }
        print('\nEntries highlighted in red are the best play EV.')
        # Make a stand
        print('EV from standing')
        print('\n                                      Dealer\'s up card')
        for duc in range(1, 12):
            label = NUM_TO_TEXT[duc]
            if duc == 1:
                print(f'        ', end="")
            else:
                if duc == 11:
                    print(f'{label:>9}')
                else:
                    print(f'{label:>9}', end="")
            
        for pht in range(16, 22):
            print(f'{pht:>7} ', end="")
            for duc in range(2, 12):
                duc_it = eleven_to_one[duc]
                play, ev_list = self.hard_hand_book_lookup(pht, duc_it)
                
                if play == 'S':
                    use_file = sys.stderr
                else:
                    use_file = sys.stdout
                if duc_it != 1:
                    print(f'{ev_list[0]:9.5}', file=use_file, end="")
                else:
                    print(f'{ev_list[0]:9.5}', file=use_file)
                sys.stdout.flush()
                sys.stderr.flush()

        # Take a hit
        print('\nEV from hitting')
        print('\n                                      Dealer\'s up card')
        for duc in range(1, 12):
            label = NUM_TO_TEXT[duc]
            if duc == 1:
                print(f'        ', end="")
            else:
                if duc == 11:
                    print(f'{label:>9}')
                else:
                    print(f'{label:>9}', end="")
            
        for pht in range(4, 21):
            print(f'{pht:>8} ', end="")
            for duc in range(2, 12):
                duc_it = eleven_to_one[duc]
                play, ev_list = self.hard_hand_book_lookup(pht, duc_it)
                if play == 'H':
                    use_file = sys.stderr
                else:
                    use_file = sys.stdout
                if duc_it != 1:
                    print(f'{ev_list[1]:9.5}', file=use_file, end="")
                else:
                    print(f'{ev_list[1]:9.5}', file=use_file)
                sys.stdout.flush()
                sys.stderr.flush()
        for pht in range(12, 21):
            soft_txt = 'soft ' + str(pht)
            print(f'{soft_txt:>8} ', end="")
            for duc in range(2, 12):
                duc_it = eleven_to_one[duc]
                ev = book[(1, pht - 11, duc_it)][2]
                if book[(1, pht - 11, duc_it)][0] == 'H':
                    use_file = sys.stderr
                else:
                    use_file = sys.stdout
                if duc_it != 1:
                    print(f'{ev:9.5}', file=use_file, end="")
                else:
                    print(f'{ev:9.5}', file=use_file)
                sys.stdout.flush()
                sys.stderr.flush()
        # Double down
        print('\nEV from doubling')
        print('\n                                      Dealer\'s up card')
        for duc in range(1, 12):
            label = NUM_TO_TEXT[duc]
            if duc == 1:
                print(f'        ', end="")
            else:
                if duc == 11:
                    print(f'{label:>9}')
                else:
                    print(f'{label:>9}', end="")
            
        for pht in range(7, 21):
            print(f'{pht:>8} ', end="")
            for duc in range(2, 12):
                duc_it = eleven_to_one[duc]
                play, ev_list = self.hard_hand_book_lookup(pht, duc_it)
                if play == 'D':
                    use_file = sys.stderr
                else:
                    use_file = sys.stdout
                if duc_it != 1:
                    print(f'{ev_list[2]:9.5}', file=use_file, end="")
                else:
                    print(f'{ev_list[2]:9.5}', file=use_file)
                sys.stdout.flush()
                sys.stderr.flush()
        for pht in range(12, 21):
            soft_txt = 'soft ' + str(pht)
            print(f'{soft_txt:>8} ', end="")
            for duc in range(2, 12):
                duc_it = eleven_to_one[duc]
                ev = book[(1, pht - 11, duc_it)][3]
                if book[(1, pht - 11, duc_it)][0] == 'D':
                    use_file = sys.stderr
                else:
                    use_file = sys.stdout
                if duc_it != 1:
                    print(f'{ev:9.5}', file=use_file, end="")
                else:
                    print(f'{ev:9.5}', file=use_file)
                sys.stdout.flush()
                sys.stderr.flush()
        # Split
        print('\nEV from splitting')
        print('\n                                      Dealer\'s up card')
        for duc in range(1, 12):
            label = NUM_TO_TEXT[duc]
            if duc == 1:
                print(f'        ', end="")
            else:
                if duc == 11:
                    print(f'{label:>8} ')
                else:
                    print(f'{label:>8} ', end="")
            
        for pair_of in range(2, 12):
            pair_txt = NUM_TO_TEXT[pair_of]
            pair_it = eleven_to_one[pair_of]
            print(f'{pair_txt:>3}, {pair_txt:<3}', end="")
            for duc in range(2, 12):
                duc_it = eleven_to_one[duc]
                play, ev_list = self.book_lookup([eleven_to_one[pair_of],
                                             eleven_to_one[pair_of]],
                                             duc_it)
                ev = ev_list[3]
                if play == 'P':
                    use_file = sys.stderr
                else:
                    use_file = sys.stdout
                if duc_it != 1:
                    print(f'{ev:9.5}', file=use_file, end="")
                else:
                    print(f'{ev:9.5}', file=use_file)
                sys.stdout.flush()
                sys.stderr.flush()
        print('\n\n')

    def hand_builder(self, fpc, spc, duc, deck=None):
        """Creates book entries for the passed hand. If there isn't a duc
        card in the deck, or a duc card after the fpc and spc cards have
        been removed from the deck, then the play is set to 'X'."""
        
        assert deck
        global book

        stand_ev_per_ddc = {}
        hit_ev_per_ddc = {}
        double_ev_per_ddc = {}

        # We want to exclude natural dealer BJ from book because we use book
        # to determine the EV and best play in the absence of a dealer BJ.
        
        if self.deck_choice == 'infinite':
            play_deck = ONE_DECK
        else:
            # Ensure the player cards and duc are in the deck.
            play_deck = deck.copy()
            hand_ok = True
            if play_deck.count(fpc) > 0:
                play_deck.remove(fpc)
            else:
                hand_ok = False
            if play_deck.count(spc) > 0:
                play_deck.remove(spc)
            else:
                hand_ok = False
            if play_deck.count(duc) > 0:
                play_deck.remove(duc)
            else:
                hand_ok = False
            if hand_ok == False:
                book[(fpc, spc, duc)] = ['X',0, 0, 0]
                print(f'(hand_builder) Deck can"t accomodate hand: ({fpc}, '
                      f'{spc}, {duc})')
                return
        
        ddcs = set(play_deck)
        if duc == 1:
            try:
                ddcs.remove(10)
            except Exception:
                pass
            ddc_deck = [card for card in play_deck if card != 10]
            ddc_dist = self.get_card_dist(ddc_deck)
        elif duc == 10:
            try:
                ddcs.remove(1)
            except Exception:
                pass
            ddc_deck = [card for card in play_deck if card != 1]
            ddc_dist = self.get_card_dist(ddc_deck)
        else:
            if self.deck_choice == 'infinite':
                ddc_dist = ONE_DECK_DIST
            else:
                ddc_dist = self.get_card_dist(play_deck)

        if DEBUG == 1:
            print(f'ddcs: {ddcs}')
            print(f'ddc_dist for ({fpc}, {spc}, {duc}): ddc_dist: {ddc_dist}')

        ev_list = [0, 0, 0]
        pht, _ = self.best_hand_from_card_list([fpc, spc])
        ddcs_len = len(ddcs)
        for ddc in ddcs:
            dealer_card_list = [duc, ddc]
            dht, _ = self.best_hand_from_card_list(dealer_card_list)
            if dht == 21:
                print(f'dealer_card_list: {dealer_card_list}')
                raise Exception
            if self.deck_choice == 'infinite':
                continue_deck = play_deck
            else:
                continue_deck = play_deck.copy()
                continue_deck.remove(ddc)

            stand_ev = self.dealer_turn(
                    [fpc, spc],
                    dealer_card_list,
                    continue_deck
                    )
            
            stand_ev_per_ddc[ddc] = stand_ev
            ev_list[0] += ddc_dist[ddc] * stand_ev

            
            if pht != 21:
                hit_ev = self.player_hit(
                        [fpc, spc],
                        dealer_card_list,
                        continue_deck
                        )

                hit_ev_per_ddc[ddc] = hit_ev
                ev_list[1] += ddc_dist[ddc] * hit_ev

                double_ev = self.player_double(
                        [fpc, spc],
                        dealer_card_list,
                        continue_deck
                        )

                double_ev_per_ddc[ddc] = double_ev
                ev_list[2] += ddc_dist[ddc] * double_ev
            else:
                hit_ev_per_ddc[ddc] = -1
                double_ev_per_ddc[ddc] = -2
                
        if DEBUG == 1:
            print(f'(hand_builder) stand_ev_per_ddc for '
                  f'({fpc}, {spc}, {duc}): '
                  f'{stand_ev_per_ddc}')
            total_stand_ev = 0
            total_hit_ev = 0
            total_double_ev = 0
            for card in ddcs:
                total_stand_ev += ddc_dist[card] * stand_ev_per_ddc[card]
                total_hit_ev += ddc_dist[card] * hit_ev_per_ddc[card]
                total_double_ev += ddc_dist[card] * double_ev_per_ddc[card]
                
            print(f'(hand_builder) total_stand_ev: {total_stand_ev}'
                  f'ev_list[0]: {ev_list[0]}')
            print(f'ev_list: {ev_list} max(ev_list): {max(ev_list)}')
            
        best_play = REV_EV_INDEX[ev_list.index(max(ev_list))]
        if pht != 21:
            book[(fpc, spc, duc)] = \
                    [best_play, ev_list[0], ev_list[1], ev_list[2]]
        else:
            book[(fpc, spc, duc)] = [best_play, ev_list[0], -1, -1]
        if best_play == 'D':
            next_best_play = self.double_check(best_play, [fpc, spc], duc)
            if next_best_play != 'D':
                book[(fpc, spc, duc)][0] = next_best_play

    def player_hit(self, player_card_list, dealer_card_list, deck):
        """Returns the ev of the passed player and dealer hands. The decision 
        to hit or stand is made by consulting the book."""
        total_ev = 0
        duc = dealer_card_list[0]

        if self.deck_choice == 'infinite':
            hit_card_dist = ONE_DECK_DIST
        else:
            hit_card_dist = self.get_card_dist(deck)

        hit_cards = set(deck)
        
        for hit_card in hit_cards:
            new_player_card_list = player_card_list.copy()
            new_player_card_list.append(hit_card)
            pht, hard_or_soft = self.best_hand_from_card_list(
                    new_player_card_list
                    )

            if pht > 21:
                continue_ev = -1
            else:
                # we don't have to check for the existance of this book_play 
                # here because the pht is higher than what was called from 
                # hard or soft hand builder, thus gauranteeing that the play 
                # (and hence EV) for the new pht is already in book since we 
                # create book plays from top to bottom.
                book_play, ev_list = self.no_split_book_lookup(
                        new_player_card_list, duc)
                book_play = self.double_check(
                        book_play, new_player_card_list, duc)
                
                if self.deck_choice == 'infinite':
                    # If we are using infinite deck, there is no reason to 
                    # call player_hit or dealer_turn because the deck 
                    # distribution is constant. So, we just use our already 
                    # calculated EV values, vastly speeding up the program.
                    continue_ev = ev_list[EV_INDEX[book_play]]
                else:
                    new_deck = deck.copy()
                    new_deck.remove(hit_card)
                    if book_play == 'S':
                        continue_ev = self.dealer_turn(
                                new_player_card_list,
                                dealer_card_list,
                                new_deck
                                )
                    elif book_play == 'H':
                        continue_ev = self.player_hit(
                                new_player_card_list,
                                dealer_card_list,
                                new_deck
                                )
                    elif book_play == 'D':
                        continue_ev = self.player_double(
                                new_player_card_list,
                                dealer_card_list,
                                new_deck
                                )
                    else:
                        print(f'book_play: {book_play} '
                              f'new_player_card_list: {new_player_card_list}')
                        raise Exception
                                                          
            total_ev += hit_card_dist[hit_card] * continue_ev
        return total_ev
    
    def player_double(self, player_card_list, dealer_card_list, deck):
        """Returns the ev of the passed player and dealer hands when the player
        gets to draw only one card."""
        total_ev = 0
        duc = dealer_card_list[0]
              
        if self.deck_choice == 'infinite':
            double_card_dist = ONE_DECK_DIST
        else:
            double_card_dist = self.get_card_dist(deck)
        double_cards = set(deck)

        for double_card in double_cards:
            new_player_card_list = player_card_list.copy()
            new_player_card_list.append(double_card)
            pht, hard_or_soft = self.best_hand_from_card_list(
                    new_player_card_list
                    )

            if pht > 21:         
                continue_ev = -1
            else:
                if self.deck_choice == 'infinite':
                    # Since we are standing after we get our double card:
                    play, ev_list = self.book_lookup(new_player_card_list,
                                                duc)
                    continue_ev = ev_list[0]
                else:
                    new_deck = deck.copy()
                    new_deck.remove(double_card)
                    continue_ev = self.dealer_turn(
                            new_player_card_list,
                            dealer_card_list,
                            new_deck
                            )
                               
            total_ev += double_card_dist[double_card] * continue_ev
        return 2 * total_ev

    def dealer_turn(self, player_card_list, dealer_card_list, deck):
        """Returns the ev of the passed player hand total, dealer card list,
        and deck (in list form). The dcc is already assigned."""

        pht, _ = self.best_hand_from_card_list(player_card_list)
        dht, hard_or_soft = self.best_hand_from_card_list(dealer_card_list)
        
        if dht == 21 and len(dealer_card_list) == 2:
            print(f'Error in dealer_turn, dealer had blackjack. dht: {dht} '
                  f'card list: {dealer_card_list}')
            raise Exception

        if dht >= 22:
            return 1
        
        if (dht == 17 and hard_or_soft == 'hard') or (dht >= 18) or \
            (dht == 17 and hard_or_soft == 'soft' and not \
                 self.dhs17_var.get()):
            # Dealer is done drawing cards. Let's see who won.
            if pht == dht:
                return 0
            elif pht > dht:
                return 1
            else:
                return -1
             
        # At this point, dealer must draw a card. So we figure the % chance of
        # dealer drawing each card value, multiply those %'s by the ev for that
        # card value, and sum together to get the total ev.

        dealer_card_set = set(deck)
        interim_ev = 0
        if self.deck_choice == 'infinite':
            card_dist = ONE_DECK_DIST
        else:
            card_dist = self.get_card_dist(deck)
            
        for dealer_card in dealer_card_set:
            new_dealer_card_list = dealer_card_list.copy()
            new_dealer_card_list.append(dealer_card)

            if self.deck_choice == 'infinite':
                new_deck = deck
            else:
                new_deck = deck.copy()
                new_deck.remove(dealer_card)
                                                        
            hand_ev = self.dealer_turn(
                              player_card_list,
                              new_dealer_card_list,
                              new_deck
                              )    
            interim_ev += card_dist[dealer_card] * \
                          hand_ev
        
        return interim_ev          

    def pair_hand_builder(self, pair_of, duc, deck):
        """Calculates the ev of splitting a pair. Assumes a player will 
        continue to split if he draws another pair_of card up to the maximum 
        allowed by MAX_SPLIT HANDS, the RSA variable for aces, and of course 
        assumming that there is another pair_of card to be drawn."""

        old_best_play, ev_list = self.book_lookup([pair_of, pair_of], duc)
        max_nonsplit_ev = max(ev_list)
        if old_best_play == 'X':
            return
        
        # The p's and m's in the variables below represent the different
        # ways that a split hand can stay at just two hands, or expand
        # to three or four hands. A 'p' represents a second card draw
        # that is a pair card and results in a new split hand. A 'm'
        # represents a second card draw that is not a pair card, and that
        # hand gets played out normally.
        
        #Pair stats
        global two_hand_count
        global three_hand_count
        global four_hand_count
        global two_hand_ev_summation_list
        global three_hand_ev_summation_list
        global four_hand_ev_summation_list
        global mm_ev_summation_list
        global p_ev_summation_list
        global mp_ev_summation_list
        global pmmm_ev_summation_list
        global mpmm_ev_summation_list
        global pp_ev_summation_list
        global pmp_ev_summation_list
        global mpp_ev_summation_list
        global pmmp_ev_summation_list
        global mpmp_ev_summation_list
        global event_hand_counts
        global ddc_is_pc_count
        

        two_hand_count = 0
        three_hand_count = 0
        four_hand_count = 0
        two_hand_ev_summation_list = [0, 0]
        three_hand_ev_summation_list = [0, 0, 0]
        four_hand_ev_summation_list = [0, 0, 0, 0]
        mm_ev_summation_list = [0, 0]
        p_ev_summation_list = [0, 0, 0]
        mp_ev_summation_list = [0, 0, 0]
        pmmm_ev_summation_list = [0, 0, 0]
        mpmm_ev_summation_list = [0, 0, 0]        
        pp_ev_summation_list = [0, 0, 0, 0]
        pmp_ev_summation_list = [0, 0, 0, 0]
        mpp_ev_summation_list = [0, 0, 0, 0]
        pmmp_ev_summation_list = [0, 0, 0, 0]
        mpmp_ev_summation_list = [0, 0, 0, 0]
        event_hand_counts = {'mm':0, 'p':0, 'mp':0, 'pmmm':0, 'mpmm':0, 
                             'pp':0, 'pmp':0, 'mpp':0, 'pmmp':0, 'mpmp':0}
        ddc_is_pc_count = {'mm':0, 'p':0, 'mp':0, 'pmmm':0, 'mpmm':0, 
                             'pp':0, 'pmp':0, 'mpp':0, 'pmmp':0, 'mpmp':0}
        
        split_ev = 0
        
        for count in range(0, SIM_MAX):
            run_ev = self.sim_play(pair_of, pair_of, duc, 'P', False, deck)
            split_ev = (run_ev + split_ev * count) / (count + 1)
            diff = abs(split_ev - max_nonsplit_ev)
            if count > 10000 and diff * count > 200:
                break
        
        # We need to compare the split EV (total_ev) with the previously 
        # determined EVs for standing, hitting and doubling to determine 
        # which is best.


        if split_ev > max_nonsplit_ev:
            book[(pair_of, pair_of, duc)][0] = 'P'
        if len(book[(pair_of, pair_of, duc)]) == 4:
            book[(pair_of, pair_of, duc)].append(split_ev)
        elif len(book[(pair_of, pair_of, duc)]) == 5:
            book[(pair_of, pair_of, duc)][4] = split_ev

        if DEBUG >= 2:
            print(f'\npair_hand_builder simulation statistics for pair of '
                  f' {pair_of} and duc {duc}')
            print(f'Number of hand simulations: {count}')            
            for event in event_hand_counts.keys():
                print(f'Event: {event} prob: '
                      f'{event_hand_counts[event] / count}') 

            if event_hand_counts['mm'] != 0:
                mm_ev_list = []
                if event_hand_counts['mm'] != 0:
                    for summ in mm_ev_summation_list:
                        mm_ev_list.append(summ / event_hand_counts['mm'])
                    print(f'mm_ev_list: {mm_ev_list}')
                    
            if event_hand_counts['p'] != 0:
                p_ev_list = []
                for summ in p_ev_summation_list:
                    p_ev_list.append(summ / event_hand_counts['p'])
                print(f'p_ev_list: {p_ev_list}')
            if event_hand_counts['mp'] != 0:
                mp_ev_list = []
                for summ in mp_ev_summation_list:
                    mp_ev_list.append(summ / event_hand_counts['mp'])
                print(f'mp_ev_list: {mp_ev_list}')
            if event_hand_counts['pmp'] != 0:
                pmp_ev_list = []
                for summ in pmp_ev_summation_list:
                    pmp_ev_list.append(summ / event_hand_counts['pmp'])
                print(f'pmp_ev_list: {pmp_ev_list}')
            if event_hand_counts['mpp'] != 0:
                mpp_ev_list = []
                for summ in mpp_ev_summation_list:
                    mpp_ev_list.append(summ / event_hand_counts['mpp'])
                print(f'mpp_ev_list: {mpp_ev_list}')         
            if event_hand_counts['pmmm'] != 0:
                pmmm_ev_list = []
                for summ in pmmm_ev_summation_list:
                    pmmm_ev_list.append(summ / event_hand_counts['pmmm'])
                print(f'pmmm_ev_list: {pmmm_ev_list}')
            if event_hand_counts['mpmm'] != 0:
                mpmm_ev_list = []
                for summ in mpmm_ev_summation_list:
                    mpmm_ev_list.append(summ / event_hand_counts['mpmm'])
                print(f'mpmm_ev_list: {mpmm_ev_list}')
            if event_hand_counts['pp'] != 0:
                pp_ev_list = []
                for summ in pp_ev_summation_list:
                    pp_ev_list.append(summ / event_hand_counts['pp'])
                print(f'pp_ev_list: {pp_ev_list}')
            if event_hand_counts['mpmp'] != 0:
                mpmp_ev_list = []
                for summ in mpmp_ev_summation_list:
                    mpmp_ev_list.append(summ / event_hand_counts['mpmp'])
                print(f'mpmp_ev_list: {mpmp_ev_list}')
            if event_hand_counts['pmmp'] != 0:
                pmmp_ev_list = []
                for summ in pmmp_ev_summation_list:
                    pmmp_ev_list.append(summ / event_hand_counts['pmmp'])
                print(f'pmmp_ev_list: {pmmp_ev_list}')        
                                       
            ddc_is_pc_chance = {}
            for event in event_hand_counts.keys():
                if event_hand_counts[event] > 0:
                    ddc_is_pc_chance[event] = ddc_is_pc_count[event] /\
                        event_hand_counts[event]
            print(f'ddc_is_pc_chance: {ddc_is_pc_chance}') 
                  
def main():
    root = tk.Tk()
    root.title('Leon\'s Blackjack Book Maker')
    root.geometry('1340x400')
    main = Book(root)
    root.mainloop()

if __name__ == '__main__':
    main()

    






                                
        
