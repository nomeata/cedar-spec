permit(
  principal in a::"66",
  action in [Action::"action"],
  resource
) when {
  (true && (principal in principal)) && (true == ([ip("6767:6767:6767:c3c3:c3c3:c3c3:c3ff:32c3/103"), ip("0.101.103.103/30"), ip("c3c3:c3c3:c3c3:c3c3::c3:c3f2/66")].containsAny([ip("47.47.195.195/14"), ip("::f236:3636:3636"), ip("0.0.0.0")])))
};
