@B0h8Y("6")
permit(
  principal,
  action in [],
  resource is a in a::"\0+"
) when {
  true && (action has "")
};
