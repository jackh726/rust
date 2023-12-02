// aux-crate:bevy_ecs=bevy_ecs.rs
// check-pass

// We currently special case bevy from emitting the `IMPLIED_BOUNDS_FROM_TRAIT_IMPL` lint.
// Otherwise, we would expect this to hit the lint.

pub trait WorldQuery {}
impl WorldQuery for &u8 {}

pub struct Query<Q: WorldQuery>(Q);

pub trait SystemParam {
    type State;
}
impl<Q: WorldQuery + 'static> SystemParam for Query<Q> {
    type State = ();
    // `Q: 'static` is required because we need the TypeId of Q ...
}

pub struct ParamSet<T: SystemParam>(T) where T::State: Sized;

fn handler<'a>(_: ParamSet<Query<&'a u8>>) {}

fn main() {}
