@k66666666("")
forbid(
  principal,
  action in [B::Action::"action"],
  resource
) when {
  ((true && ([[resource, resource, resource], [resource, resource, resource], [resource, resource, resource]] == [[resource, resource, resource], [principal, principal, principal], [resource, resource, principal]])) && ((if ((ip("0:c3:c3c3:c3c3:72:7474:61c3:c3c3")) == (ip("0.0.0.0"))) then (ip("0.0.0.0")) else (ip("0.0.0.0"))) == (ip("0.0.0.0")))) && false
};
