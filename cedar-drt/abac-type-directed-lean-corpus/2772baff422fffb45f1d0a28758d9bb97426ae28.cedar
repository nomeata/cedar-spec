permit(
  principal,
  action == Action::"action",
  resource == Ie::"55555555555555,,,,,,,,,,,,,,,,,,,,,,,,,,,,,"
) when {
  (true && (false == (if (!true) then (!true) else ((ip("3636:a036:3636:ffff:b2ff:ff38:3832:ffff")).isLoopback())))) && (!(!(!true)))
};
