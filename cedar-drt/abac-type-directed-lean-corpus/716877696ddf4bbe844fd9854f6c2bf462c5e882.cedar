permit(
  principal,
  action in [Action::"action"],
  resource is h in BcpD::"\0666"
) when {
  false
};
