@r("")
permit(
  principal,
  action in [Action::"6"],
  resource
) when {
  ((true && ((if ((ip("c9c9:c9c9:c9c4:ff7e:5bff:ff7b:2a2a:2a36/772")).isInRange(ip("5b5b:5ba5:5b5b:5b5b:5b5b:5b5b:5b5b:5b5b/91"))) then 3906369333256140543 else 3906369333256140543) == 3906369333256140543)) && (resource in a::"")) && false
};
