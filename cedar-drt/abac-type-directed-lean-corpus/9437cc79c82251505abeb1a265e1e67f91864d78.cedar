forbid(
  principal == a::"",
  action in [Action::"action"],
  resource
) when {
  ((true && ([[ip("c3:c3c3:c3c3:c3c3:c3c3:c3c3:c3c3:c3c3"), ip("34.34.34.34"), ip("34.34.34.34")], [ip("34.34.34.34"), ip("0.1.34.34")], [ip("c3c3:c3c3:c3c3:c3c3:c3c3:c3c3:c3c3:c3c3/66"), ip("0.0.0.0"), ip("0.0.0.0")]] == [])) && false) && false
};
