@k66666666("")
forbid(
  principal,
  action in [B::Action::"action"],
  resource
) when {
  ((true && ([[ip("c3:c3c3:c3c3:c3c3:c3c3:c3c3:c3c3:c3c3"), ip("c3c3:c3c3:c3c3:c3c3:c3c3:c3c3:c3c3:c3c3/66"), ip("c3:c3c3:c3c3:c3c3:c3c3:c3c3:c3c3:c3c3")], [ip("::c3c3:c3c3:c3c3:c3c3:c3c3"), ip("0.0.0.0"), ip("0.0.0.0")], []] == [])) && false) && false
};
