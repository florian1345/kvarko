use kvarko_model::movement::Move;

pub struct MoveOrdering {
    children: Vec<(Move, Option<MoveOrdering>)>
}

impl MoveOrdering {

    pub fn push(&mut self, mov: Move, ordering: Option<MoveOrdering>) {
        self.children.push((mov, ordering))
    }

    pub fn get(&self, index: usize) -> Option<(Move, Option<&MoveOrdering>)> {
        self.children.get(index)
            .map(|(m, o)| (*m, o.as_ref()))
    }

    pub fn get_mut(&mut self, index: usize)
            -> Option<(Move, Option<&mut MoveOrdering>)> {
        self.children.get_mut(index)
            .map(|(m, o)| (*m, o.as_mut()))
    }

    pub fn swap(&mut self, index_1: usize, index_2: usize) {
        self.children.swap(index_1, index_2)
    }

    pub fn moves(&self) -> impl Iterator<Item = Move> + '_ {
        self.children.iter().map(|(m, _)| *m)
    }

    pub fn iter(&self)
            -> impl Iterator<Item = (Move, Option<&MoveOrdering>)> + '_ {
        self.children.iter().map(|(m, o)| (*m, o.as_ref()))
    }

    pub fn iter_mut(&mut self)
            -> impl Iterator<Item = (Move, Option<&mut MoveOrdering>)> + '_ {
        self.children.iter_mut().map(|(m, o)| (*m, o.as_mut()))
    }
}
