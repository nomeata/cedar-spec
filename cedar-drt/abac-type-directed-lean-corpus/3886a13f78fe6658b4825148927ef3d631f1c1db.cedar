forbid(
  principal == a::"",
  action in [Action::"action"],
  resource
) when {
  ((true && ([[ip("3636:a036:a4c3:c3c3:c3c3:c3c3:c3c3:c3c3"), ip("c3c3:c3c3:83c3:c3c3:c3c3:c3c3:c3c3:c3c3"), ip("c3c3:c3c3:c3c3:c3c3::c3:c3c3")], [ip("49.127.0.0/19"), ip("c3c3:c3c3:c3c3:c3c3:c3c3:c3c3:c3c3:c3c3/66"), ip("c3c3:c3c3:c3c3::c3:c3c3:c3c3/66")], [ip("49.127.0.0/30"), ip("c3c3:c3c3:c3c3:c367:6767:6767:c3c3:c3c3/66"), ip("da:dada:da36:3636:c3c3:c3c3:c3c3:c3c3")]] == [])) && false) && false
};
