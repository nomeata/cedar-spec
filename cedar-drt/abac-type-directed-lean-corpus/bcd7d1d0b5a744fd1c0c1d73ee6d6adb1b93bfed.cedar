permit(
  principal == fB::Es::fB::a::"65\u{1}",
  action in [fB::Es::fB::Action::""],
  resource == fB::Es::fB::a::"65\u{1}"
) when {
  ((true && (if (if (if true then true else true) then (if true then false else false) else (resource is fB::Es::fB::a)) then (resource is fB::Es::fB::a) else (resource is fB::Es::fB::a))) && (if (if (if true then true else false) then (resource is fB::Es::fB::a) else (resource is fB::Es::fB::a)) then (resource is fB::Es::fB::a) else (resource is fB::Es::fB::a))) && (resource is fB::Es::fB::a)
};
